#!/usr/bin/env python3
"""Flip one mutation hypothesis in a proof module and check that the proof breaks.

usage: scripts/flip_test.py <Module> <M_X> [<M_Y> ...]

For each mutation named, copies the module chain and <Module>_proof.tla to a
scratch directory, rewrites every `Mut # "M_X"` in the proof module to
`Mut = "M_X"`, and runs tools/tlapm --cleanfp --strict on the copy. The
prover must report failed obligations: a proof that survives with the
hypothesis flipped is proving something the mutation does not break. Prints
one line per mutation; the copies are deleted and nothing is written to the
tree (a mutated proof is not an artefact). Exits non-zero if any flipped
proof still proves, or a mutation's hypothesis does not occur in the module.
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tlc_rows import ROOT, extends_chain  # noqa: E402


def main(argv):
    if len(argv) < 2:
        raise SystemExit(__doc__)
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
            p = subprocess.run([os.path.join(ROOT, "tools", "tlapm"), "--cleanfp", "--strict",
                                "--cache-dir", os.path.join(tmp, "cache"), proof + ".tla"],
                               cwd=tmp, capture_output=True, text=True)
            out = p.stdout + p.stderr
            m = re.search(r"(\d+)/(\d+) obligations? failed", out)
            if m:
                print(f"{module} flip {mut} ({n} hypotheses flipped): {m.group(0)} - as required")
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
