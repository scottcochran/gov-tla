#!/usr/bin/env python3
"""Flip one mutation hypothesis in a proof module and check that the proof breaks.

usage: scripts/flip_test.py <Module> [--threads N] <M_X> [<M_Y> ...]

For each mutation named, copies the module chain and <Module>_proof.tla to a
scratch directory, rewrites every `Mut # "M_X"` in the proof module to
`Mut = "M_X"`, and runs tools/tlapm --cleanfp --strict on the copy. The
prover must report failed obligations: a proof that survives with the
hypothesis flipped is proving something the mutation does not break. Each
failure is attributed to the THEOREM or LEMMA that contains it, and a flip
passes only if some failure lies in a statement, other than SafeAlways,
whose text carried the flipped hypothesis. (SafeAlways's Mut = "none"
citation steps fail under any flip; a failure elsewhere can be a timeout on
a loaded machine.) Prints one line per mutation; the copies are deleted,
the prover's backends are killed with it, and nothing is written to the
tree (a mutated proof is not an artefact). Exits non-zero if any flipped
proof still proves, fails nowhere that carries the hypothesis, stops
without an obligation count (ERROR), or a mutation's hypothesis does not
occur in the module.
"""
import os
import re
import shutil
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tlc_rows import ROOT, extends_chain, run_group  # noqa: E402


def statement_spans(text):
    """(first line, last line, name) of every THEOREM/LEMMA in text."""
    ms = list(re.finditer(r"^(?:THEOREM|LEMMA|COROLLARY|PROPOSITION)\s+(\w+)\s*==", text, re.M))
    spans = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        spans.append((m.start(), end, m.group(1)))
    return spans


def failing_statements(text, out, proof):
    """Names of the THEOREMs/LEMMAs containing each failed obligation."""
    starts = [(text[:m.start()].count("\n") + 1, m.group(1)) for m in re.finditer(
        r"^(?:THEOREM|LEMMA|COROLLARY|PROPOSITION)\s+(\w+)\s*==", text, re.M)]
    names = []
    lines = out.splitlines()
    for i, line in enumerate(lines):
        if "Could not prove or check" in line and i > 0:
            m = re.search(r'File "\./' + re.escape(proof) + r'\.tla", line (\d+)', lines[i - 1])
            if m:
                ln = int(m.group(1))
                owner = [name for start, name in starts if start <= ln]
                name = owner[-1] if owner else f"line {ln}"
                if name not in names:
                    names.append(name)
    return names


def main(argv):
    if len(argv) < 2:
        raise SystemExit(__doc__)
    threads = None
    if "--threads" in argv:
        i = argv.index("--threads")
        threads = argv[i + 1]
        argv = argv[:i] + argv[i + 2:]
    module = argv[0].removesuffix(".tla").removesuffix("_proof")
    proof = module + "_proof"
    bad = 0
    for mut in argv[1:]:
        tmp = tempfile.mkdtemp(prefix=f"flip_{module}_{mut}_")
        try:
            for m in extends_chain(proof):
                shutil.copy(os.path.join(ROOT, m + ".tla"), tmp)
            path = os.path.join(tmp, proof + ".tla")
            text = open(path).read()
            pat = re.compile(r'Mut\s*#\s*"' + re.escape(mut) + '"')
            n = len(pat.findall(text))
            if n == 0:
                print(f"{module} flip {mut}: no `Mut # \"{mut}\"` hypothesis in {proof}.tla"); bad += 1
                continue
            open(path, "w").write(pat.sub(f'Mut = "{mut}"', text))
            cmd = [os.path.join(ROOT, "tools", "tlapm"), "--cleanfp", "--strict",
                   "--cache-dir", os.path.join(tmp, "cache")]
            if threads:
                cmd += ["--threads", threads]
            code, out = run_group(cmd + [proof + ".tla"], tmp)
            m = re.search(r"(\d+)/(\d+) obligations? failed", out)
            carriers = {name for a, b, name in statement_spans(text) if pat.search(text[a:b])}
            if m:
                where = failing_statements(text, out, proof)
                relevant = [w for w in where if w != "SafeAlways" and w in carriers]
                verdict = "as required" if relevant else \
                    "fails nowhere that carries the hypothesis - not load-bearing"
                bad += not relevant
                print(f"{module} flip {mut} ({n} hypotheses flipped): {m.group(0)} in "
                      f"{', '.join(where) or '?'} - {verdict}")
            elif re.search(r"All \d+ obligations? proved", out):
                print(f"{module} flip {mut} ({n} hypotheses flipped): "
                      f"{re.search(r'All \d+ obligations? proved', out).group(0)} - the hypothesis is NOT load-bearing")
                bad += 1
            else:
                print(f"{module} flip {mut}: ERROR, no obligation count (tlapm exit {code})")
                bad += 1
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
