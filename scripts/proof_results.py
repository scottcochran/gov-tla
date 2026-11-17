#!/usr/bin/env python3
"""Prove <Module>_proof.tla and write its dated proof results file.

usage: scripts/proof_results.py <Module> [--threads N] [--dry-run | --out PATH]

Runs tools/tlapm --cleanfp --strict on <Module>_proof.tla with a throwaway
cache directory, so nothing is taken from an earlier run and nothing is
written beside the module. Only the final obligation count and the exit
status are read; a backend's failure line is noise when another backend
closed the obligation.

The results file, results/<Module>-proof-results-<YYYY.MM.DD>.txt, prints
the sha256 of every repository module in the EXTENDS chain on one Modules:
line (dependencies first, the proof module last), the prover's identity and
digest on a Prover: line, the TLC results file that holds the mutations'
counterexamples, the named assumptions, every THEOREM with its statement,
every LEMMA by name, and the obligation count. It is written only when every
obligation is proved, is never overwritten (a rerun that reproduces it says
so; one that differs gets a letter suffix), and the script exits non-zero
on any failed obligation or an unpinned prover (unless TLAPM_UNPINNED=1).

The Prover: and Backends: lines of a pinned prover come from tools/TLAPS-PIN.
An unpinned prover is described by what the binary reports of itself
(tlapm --config: its commit and its backends' versions), never by the pin,
so the file names the build that ran.

--dry-run prints the file instead of writing it. --out PATH writes it to
PATH, outside results/ and whatever is there: CI uses it to compare a fresh
run with the committed file (scripts/compare_results.py).
"""
import datetime
import glob
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tlc_rows import ROOT, extends_chain, pin, run_group, sha256  # noqa: E402


def prover_binary():
    return os.environ.get("TLAPM") or os.path.join(
        ROOT, "tools", f"tlaps-{pin('TLAPS-PIN', 'version')}", "bin", "tlapm")


def prover_lines(binary, digest, pinned):
    """The Prover: and Backends: lines. A pinned binary is described by
    tools/TLAPS-PIN, as every committed results file is; any other binary by
    what it reports of itself, so that the file never names a build that did
    not run."""
    if pinned:
        return (f"Prover: tlapm {pin('TLAPS-PIN', 'version')} commit {pin('TLAPS-PIN', 'commit')} "
                f"({pin('TLAPS-PIN', 'platform')}) sha256 {digest}",
                f"Backends: {pin('TLAPS-PIN', 'backends')}")
    try:
        config = subprocess.run([binary, "--config"], capture_output=True, text=True,
                                timeout=120).stdout
    except (OSError, subprocess.TimeoutExpired):
        config = ""
    commit = re.search(r'^version == "([^"]+)"', config, re.M)
    backends = re.findall(r'^(\S+) version == "([^"]*)"', config, re.M)
    plat = {("Linux", "x86_64"): "x86_64-linux-gnu", ("Darwin", "arm64"): "arm64-darwin"}.get(
        (platform.system(), platform.machine()), f"{platform.machine()}-{platform.system().lower()}")
    return (f"Prover: tlapm commit {commit.group(1) if commit else 'unknown'} ({plat}) "
            f"sha256 {digest} (NOT the pin in tools/TLAPS-PIN; commit and backends as the binary reports them)",
            "Backends: " + ("; ".join(f"{name} {v}" for name, v in backends)
                            if backends else "unknown (tlapm --config reported none)"))


def statements(text):
    """Named ASSUMEs, THEOREMs (with their statement) and LEMMAs, in order."""
    out = []
    pat = re.compile(r"^(ASSUME|THEOREM|LEMMA|COROLLARY|PROPOSITION)\s+(\w+)\s*==", re.M)
    for m in pat.finditer(text):
        kind, name = m.group(1), m.group(2)
        rest = text[m.end():]
        stop = re.search(r"^\s*(<\d+>|BY\b|PROOF\b|OBVIOUS\b|OMITTED\b)|^\S", rest, re.M)
        body = rest[:stop.start()] if stop else rest
        body = re.sub(r"\\\*[^\n]*", "", body)
        body = " ".join(body.split())
        out.append((kind, name, body))
    return out


def main(argv):
    args = [a for a in argv if not a.startswith("-")]
    threads = None
    out_path = None
    for i, a in enumerate(argv):
        if a == "--threads":
            threads = argv[i + 1]
            args.remove(threads)
        if a == "--out":
            out_path = os.path.abspath(argv[i + 1])
            args.remove(argv[i + 1])
    if len(args) != 1:
        raise SystemExit(__doc__)
    module = args[0].removesuffix(".tla").removesuffix("_proof")
    proof = module + "_proof"
    proof_path = os.path.join(ROOT, proof + ".tla")
    if not os.path.exists(proof_path):
        raise SystemExit(f"{proof}.tla not found")
    binary = prover_binary()
    prover_sha = sha256(binary)
    pinned = prover_sha == pin("TLAPS-PIN", "binary_sha256")
    if not pinned and not os.environ.get("TLAPM_UNPINNED"):
        raise SystemExit(f"{binary} is sha256 {prover_sha}, not the pin in tools/TLAPS-PIN; "
                         "set TLAPM_UNPINNED=1 to run it anyway")

    # Read what the results file will describe before the prover runs, so an
    # edit made during the run cannot make the file describe text it did not prove.
    chain = extends_chain(proof)
    digests = [(m, sha256(os.path.join(ROOT, m + ".tla"))) for m in chain]
    text = open(proof_path).read()
    tlc = sorted(glob.glob(os.path.join(ROOT, "results", f"{module}-results-*.txt")))
    tlc_line = (f"results/{os.path.basename(tlc[-1])} sha256 {sha256(tlc[-1])}" if tlc else "none")

    cache = tempfile.mkdtemp(prefix=f"tlapm_{module}_")
    try:
        cmd = [os.path.join(ROOT, "tools", "tlapm"), "--cleanfp", "--strict",
               "--cache-dir", cache]
        if threads:
            cmd += ["--threads", threads]
        cmd.append(proof + ".tla")
        code, out = run_group(cmd, ROOT, env=dict(os.environ, TLAPM=binary))
    finally:
        shutil.rmtree(cache, ignore_errors=True)
    if any(sha256(os.path.join(ROOT, m + ".tla")) != d for m, d in digests):
        print(f"{proof}.tla or a module it extends changed during the run; no results file written.")
        return 1
    ok_m = re.search(r"All (\d+) obligations? proved", out)
    fail_m = re.search(r"(\d+)/(\d+) obligations? failed", out)
    proved = bool(ok_m) and code == 0 and not fail_m
    if proved:
        count = f"All {ok_m.group(1)} obligations proved."
    elif fail_m:
        count = f"{fail_m.group(1)}/{fail_m.group(2)} obligations failed."
    else:
        count = f"no obligation count (tlapm exit {code})"
    if not proved:
        errs = [l for l in out.splitlines() if "JAVA_TOOL_OPTIONS" not in l]
        print("\n".join(errs[-200:]), file=sys.stderr)
        print(f"\n{proof}.tla: {count} No results file written.")
        return 1

    date = datetime.date.today().strftime("%Y.%m.%d")
    lines = [
        f"gov-tla - {proof}.tla, TLAPS proof results {date}",
        "Generated by scripts/proof_results.py; never edited. Command: tools/tlapm --cleanfp --strict "
        f"--cache-dir <tmp> {proof}.tla",
        "Modules: " + " ".join(f"{m}.tla {d}" for m, d in digests),
        *prover_lines(binary, prover_sha, pinned),
        "TLC results (the mutations' counterexamples and the witnesses): "
        + tlc_line,
        "Words: proved means every obligation below was discharged by the prover under the named "
        "assumptions and each theorem's hypotheses; it is not a claim about any constant the "
        "assumptions exclude, nor about law or practice",
        "",
    ]
    for kind, name, body in statements(text):
        if kind == "LEMMA":
            continue
        lines.append(f"{kind} {name} == {body}")
    lemmas = [n for k, n, _ in statements(text) if k == "LEMMA"]
    if lemmas:
        lines += ["", f"LEMMAS ({len(lemmas)}): " + ", ".join(lemmas)]
    lines += ["", f"Result: {count}"]
    out_text = "\n".join(lines) + "\n"

    if "--dry-run" in argv:
        print(out_text)
        return 0
    if out_path:
        open(out_path, "w").write(out_text)
        print(f"wrote {out_path} (not in results/): {count}")
        return 0
    os.makedirs(os.path.join(ROOT, "results"), exist_ok=True)
    base = os.path.join(ROOT, "results", f"{module}-proof-results-{date}")
    for suffix in [""] + list("bcdefghijklmnopqrstuvwxyz"):
        path = f"{base}{suffix}.txt"
        if not os.path.exists(path):
            open(path, "w").write(out_text)
            print(f"wrote {os.path.relpath(path, ROOT)}: {count}")
            break
        if open(path).read() == out_text:
            print(f"reproduced {os.path.relpath(path, ROOT)} byte for byte: {count}")
            break
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
