#!/usr/bin/env python3
"""Run a module's TLC row list and write its dated results file.

usage: scripts/tlc_rows.py rows/<Module>-rows.txt [-j N] [--only a,b] [--dry-run]

The row list is the only input. Its header comments give the module, a title,
the prose expectation, the default constants and any extra .cfg lines; each
row names one TLC run and the verdict it must give:

    # module: Constitution
    # title: Constitution.tla - the procedural core of Articles I, II and V
    # expected: Mut = "none" HOLDS on every property; each mutation ...
    # const: Persons = {p1, p2, p3}
    # cfg: CONSTRAINT Bound
    name  mut  spec  kind  property  expected  [KEY=value ...]

kind is INVARIANT, PROPERTY (temporal or action property), DEADLOCK (the
property as an invariant with TLC's deadlock check on) or SIMULATE (the
property as an invariant, random behaviours). expected is HOLDS,
COUNTEREXAMPLE, DEADLOCK (DEADLOCK rows only) or NO-ERROR-SAMPLED (SIMULATE
rows only). KEY=value pairs override a constant (Persons={p1,p2}, no spaces),
or set states=N (assert the exact distinct-state count), depth=D, num=N,
seed=S (SIMULATE rows), or constraint=Op (add CONSTRAINT Op for this row).

Every row runs with -workers 1 so a counterexample row's state count is
reproducible; PROPERTY rows add -fp 0 for the same reason; INVARIANT and
PROPERTY rows pass -deadlock (DEADLOCK rows exist to audit that flag). The
results file names the checker and every repository module in the EXTENDS
chain by sha256, prints the rows, and is written as
results/<Module>-results-<YYYY.MM.DD>.txt. A file is never overwritten: a
rerun that reproduces it byte for byte says so, a rerun that differs is
written beside it with a letter suffix, and a run with any row not as
expected writes nothing. The script exits non-zero if the
list has no rows, if any row is ERROR or not as expected, or if the jar is
not the pinned one (unless TLC_UNPINNED=1). --only and --dry-run run rows
without writing a results file.
"""
import concurrent.futures as cf
import datetime
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
JAR = os.environ.get("TLA_JAR", os.path.join(ROOT, "tools", "tla2tools.jar"))
KINDS = {"INVARIANT", "PROPERTY", "DEADLOCK", "SIMULATE"}
VERDICTS = {"HOLDS", "COUNTEREXAMPLE", "DEADLOCK", "NO-ERROR-SAMPLED"}
OPTS = {"states", "depth", "num", "seed", "constraint"}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def pin(name, key):
    for line in open(os.path.join(ROOT, "tools", name)):
        if line.startswith(key + " "):
            return line.split(" ", 1)[1].strip()
    raise SystemExit(f"tools/{name} has no {key} line")


def extends_chain(module, seen=None):
    """The module and every repository module it EXTENDS, dependencies first."""
    seen = [] if seen is None else seen
    path = os.path.join(ROOT, module + ".tla")
    if module in seen or not os.path.exists(path):
        return seen
    text = open(path).read()
    m = re.search(r"^EXTENDS\s+([^\n]*)", text, re.M)
    if m:
        for dep in [d.strip() for d in m.group(1).split(",")]:
            extends_chain(dep, seen)
    seen.append(module)
    return seen


def run_group(cmd, cwd, env=None):
    """Run cmd in its own process group and kill the whole group when it ends.

    tlapm starts backend processes (Z3, Zenon, Isabelle) that can outlive a
    timeout or tlapm itself; killing the group stops them from loading the
    machine after the run that started them is over.
    """
    import signal
    p = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True, start_new_session=True)
    try:
        out, _ = p.communicate()
    finally:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
    return p.returncode, out or ""


def parse_rows(path):
    meta = {"const": [], "cfg": [], "expected": [], "title": [], "module": []}
    rows = []
    for n, raw in enumerate(open(path), 1):
        line = raw.rstrip("\n")
        if not line.strip():
            continue
        if line.startswith("#"):
            m = re.match(r"#\s*(module|title|expected|const|cfg):\s?(.*)$", line)
            if m:
                meta[m.group(1)].append(m.group(2).rstrip())
            continue
        f = line.split()
        if len(f) < 6:
            raise SystemExit(f"{path}:{n}: a row needs name mut spec kind property expected")
        name, mut, spec, kind, prop, exp = f[:6]
        if kind not in KINDS:
            raise SystemExit(f"{path}:{n}: unknown kind {kind}")
        if exp not in VERDICTS:
            raise SystemExit(f"{path}:{n}: unknown expected verdict {exp}")
        opts, consts = {}, {}
        for kv in f[6:]:
            if "=" not in kv:
                raise SystemExit(f"{path}:{n}: {kv} is not KEY=value")
            k, v = kv.split("=", 1)
            (opts if k in OPTS else consts)[k] = v
        rows.append(dict(name=name, mut=mut, spec=spec, kind=kind, prop=prop,
                         exp=exp, opts=opts, consts=consts, line=n))
    if len(meta["module"]) != 1:
        raise SystemExit(f"{path}: exactly one '# module:' line is required")
    names = [r["name"] for r in rows]
    dup = {x for x in names if names.count(x) > 1}
    if dup:
        raise SystemExit(f"{path}: duplicate row names {sorted(dup)}")
    return meta, rows


def default_consts(meta):
    out = []
    for c in meta["const"]:
        if "=" not in c:
            raise SystemExit(f"'# const: {c}' is not NAME = value")
        k, v = c.split("=", 1)
        out.append((k.strip(), v.strip()))
    return out


def run_row(module, meta, row):
    tmp = tempfile.mkdtemp(prefix=f"tlc_{row['name']}_")
    try:
        consts = dict(default_consts(meta))
        consts["Mut"] = f'"{row["mut"]}"'
        for k, v in row["consts"].items():
            consts[k] = v.replace(",", ", ")
        cfg = [f"SPECIFICATION {row['spec']}", "CONSTANTS"]
        cfg += [f"  {k} = {v}" for k, v in consts.items()]
        cfg += meta["cfg"]
        if "constraint" in row["opts"]:
            cfg.append(f"CONSTRAINT {row['opts']['constraint']}")
        cfg.append(("PROPERTY " if row["kind"] == "PROPERTY" else "INVARIANT ") + row["prop"])
        # TLC runs on a copy of the module chain in the temp directory, so the
        # trace files it writes after a counterexample never land in the tree.
        for m in extends_chain(module):
            shutil.copy(os.path.join(ROOT, m + ".tla"), tmp)
        cfg_path = os.path.join(tmp, "MC.cfg")
        open(cfg_path, "w").write("\n".join(cfg) + "\n")
        cmd = ["java", "-XX:+UseParallelGC", f"-Xmx{os.environ.get('TLC_XMX', '2g')}",
               f"-Djava.io.tmpdir={tmp}", "-cp", JAR, "tlc2.TLC",
               "-config", cfg_path, "-workers", "1", "-metadir", os.path.join(tmp, "meta")]
        if row["kind"] in ("INVARIANT", "PROPERTY"):
            cmd.append("-deadlock")
        if row["kind"] == "PROPERTY":
            cmd += ["-fp", "0"]
        if row["kind"] == "SIMULATE":
            o = row["opts"]
            cmd += ["-deadlock", "-simulate", f"num={o.get('num', '10000')}",
                    "-depth", o.get("depth", "40"), "-seed", o.get("seed", "1")]
        cmd.append(module + ".tla")
        p = subprocess.run(cmd, cwd=tmp, capture_output=True, text=True)
        out = p.stdout + p.stderr
        if "Deadlock reached" in out:
            verdict = "DEADLOCK"
        elif re.search(r"is violated|were violated", out):
            verdict = "COUNTEREXAMPLE"
        elif "No error has been found" in out:
            verdict = "HOLDS"
        elif row["kind"] == "SIMULATE" and p.returncode == 0 and "Finished in" in out \
                and not re.search(r"^Error", out, re.M):
            verdict = "NO-ERROR-SAMPLED"
        else:
            verdict = "ERROR"
        if verdict == "HOLDS" and row["kind"] == "SIMULATE":
            verdict = "NO-ERROR-SAMPLED"
        m = re.findall(r"([0-9,]+) distinct states found", out)
        states = m[-1].replace(",", "") if m else ""
        if row["kind"] == "SIMULATE":
            m = re.findall(r"Progress: ([0-9,]+) states checked", out)
            states = m[-1].replace(",", "") if m else ""
        ok = verdict == row["exp"]
        if ok and "states" in row["opts"] and states != row["opts"]["states"]:
            ok = False
        return verdict, states, ok, (out if verdict == "ERROR" or not ok else "")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def format_row(row, verdict, states, ok):
    what = row["prop"] if row["kind"] == "INVARIANT" else f"{row['kind']} {row['prop']}"
    if row["kind"] == "SIMULATE":
        o = row["opts"]
        what += f" (simulate depth={o.get('depth', '40')} traces={o.get('num', '10000')} seed={o.get('seed', '1')})"
    extra = "".join(f" {k}={v}" for k, v in row["consts"].items())
    count = (f"{states} states checked" if row["kind"] == "SIMULATE"
             else f"{states} distinct states") if states else "no state count"
    mark = "as expected" if ok else f"UNEXPECTED (expected {row['exp']}" + (
        f", states={row['opts']['states']}" if "states" in row["opts"] else "") + ")"
    return (f"{row['name']} | Mut={row['mut']} | {row['spec']}{extra} | {what} | "
            f"{verdict} | {count} | {mark}")


def main(argv):
    args = [a for a in argv if not a.startswith("-")]
    jobs = 1
    only = None
    dry = "--dry-run" in argv
    for i, a in enumerate(argv):
        if a == "-j":
            jobs = int(argv[i + 1]); args.remove(argv[i + 1])
        if a == "--only":
            only = set(argv[i + 1].split(",")); args.remove(argv[i + 1])
    if len(args) != 1:
        raise SystemExit(__doc__)
    rows_path = os.path.abspath(args[0])
    meta, rows = parse_rows(rows_path)
    module = meta["module"][0].strip()
    if only:
        rows = [r for r in rows if r["name"] in only]
        dry = True
    if not rows:
        print("no rows to run", file=sys.stderr)
        return 1
    if not os.path.exists(JAR):
        raise SystemExit(f"{JAR} not found; run ./install-tla.sh")
    jar_sha = sha256(JAR)
    if jar_sha != pin("TLC-PIN", "jar_sha256") and not os.environ.get("TLC_UNPINNED"):
        raise SystemExit(f"{JAR} is sha256 {jar_sha}, not the pin in tools/TLC-PIN; "
                         "set TLC_UNPINNED=1 to run it anyway")

    results = [None] * len(rows)
    with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
        futs = {ex.submit(run_row, module, meta, r): i for i, r in enumerate(rows)}
        for fut in cf.as_completed(futs):
            i = futs[fut]
            verdict, states, ok, out = fut.result()
            results[i] = (verdict, states, ok)
            print(format_row(rows[i], verdict, states, ok), flush=True)
            if out:
                tail = [l for l in out.rstrip().splitlines() if "JAVA_TOOL_OPTIONS" not in l]
                print("\n".join(tail[-30:]), file=sys.stderr)

    bad = [r["name"] for r, (v, s, ok) in zip(rows, results) if not ok]
    errors = [r["name"] for r, (v, s, ok) in zip(rows, results) if v == "ERROR"]
    date = datetime.date.today().strftime("%Y.%m.%d")
    chain = extends_chain(module)
    lines = [
        f"gov-tla - {' '.join(meta['title']) or module + '.tla'}",
        f"TLC results {date}, generated by scripts/tlc_rows.py from {os.path.relpath(rows_path, ROOT)}; never edited",
        f"Checker: tla2tools.jar {pin('TLC-PIN', 'version')} ({pin('TLC-PIN', 'tlc')}) sha256 {jar_sha}"
        + ("" if jar_sha == pin("TLC-PIN", "jar_sha256") else " (NOT the pin in tools/TLC-PIN)"),
        "Modules: " + " ".join(f"{m}.tla {sha256(os.path.join(ROOT, m + '.tla'))}" for m in chain),
        f"Rows: {os.path.relpath(rows_path, ROOT)} sha256 {sha256(rows_path)}",
        "Constants: " + "; ".join(f"{k} = {v}" for k, v in default_consts(meta))
        + " (Mut and any KEY=value on a row override these)",
    ]
    lines += [f"Config: {c}" for c in meta["cfg"]]
    lines += [f"Expected: {' '.join(meta['expected'])}",
              "Flags: -workers 1; -deadlock on INVARIANT and PROPERTY rows; -fp 0 on PROPERTY rows",
              "Words: HOLDS and COUNTEREXAMPLE are checked results at these constants (every reachable state);"
              " NO-ERROR-SAMPLED is a sample, never a check; none of them is a proof",
              ""]
    lines += [format_row(r, *res) for r, res in zip(rows, results)]
    lines += ["", f"{len(rows)} rows: {len(rows) - len(bad)} as expected, {len(bad)} not"
              + (f" ({', '.join(bad)})" if bad else "") + f", {len(errors)} ERROR"]
    text = "\n".join(lines) + "\n"

    if dry or bad:
        print("\n(no results file written: " + ("dry run" if dry else "rows not as expected") + ")")
    else:
        os.makedirs(os.path.join(ROOT, "results"), exist_ok=True)
        base = os.path.join(ROOT, "results", f"{module}-results-{date}")
        for suffix in [""] + list("bcdefghijklmnopqrstuvwxyz"):
            path = f"{base}{suffix}.txt"
            if not os.path.exists(path):
                open(path, "w").write(text)
                print(f"\nwrote {os.path.relpath(path, ROOT)}")
                break
            if open(path).read() == text:
                print(f"\nreproduced {os.path.relpath(path, ROOT)} byte for byte")
                break
    print(lines[-1])
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
