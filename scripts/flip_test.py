#!/usr/bin/env python3
"""Flip one mutation hypothesis in a proof module and check that the proof breaks.

usage: scripts/flip_test.py <Module> [--threads N] <M_X> [<M_Y> ...]

For each mutation named, copies the module chain and <Module>_proof.tla to a
scratch directory, rewrites every `Mut # "M_X"` in the proof module to
`Mut = "M_X"`, and runs tools/tlapm --cleanfp --strict on the copy. The
prover must report failed obligations: a proof that survives with the
hypothesis flipped is proving something the mutation does not break. Each
failure is attributed to the THEOREM or LEMMA that contains it, and a flip
passes only if some failure lies outside SafeAlways (whose Mut = "none"
hypothesis makes its citation steps fail under any flip, so a failure there
alone shows nothing about the property's own lemmas). Prints one line per
mutation; the copies are deleted and nothing is written to the tree (a
mutated proof is not an artefact). Exits non-zero if any flipped proof
still proves, fails only in SafeAlways, or a mutation's hypothesis does not
occur in the module.
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tlc_rows import ROOT, extends_chain  # noqa: E402


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
            p = subprocess.run(cmd + [proof + ".tla"], cwd=tmp, capture_output=True, text=True)
            out = p.stdout + p.stderr
            m = re.search(r"(\d+)/(\d+) obligations? failed", out)
            if m:
                where = failing_statements(text, out, proof)
                outside = [w for w in where if w != "SafeAlways"]
                verdict = "as required" if outside else "ONLY in SafeAlways - not load-bearing"
                bad += not outside
                print(f"{module} flip {mut} ({n} hypotheses flipped): {m.group(0)} in "
                      f"{', '.join(where) or '?'} - {verdict}")
            else:
                ok = re.search(r"All \d+ obligations? proved", out)
                print(f"{module} flip {mut} ({n} hypotheses flipped): "
                      f"{ok.group(0) if ok else 'no count'} - the hypothesis is NOT load-bearing")
                bad += 1
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
