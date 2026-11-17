#!/usr/bin/env python3
"""Say which modules CI must check, from the files a change touched.

usage: git diff --name-only <base> <head> | scripts/ci_plan.py
       scripts/ci_plan.py --all

Prints two lines for $GITHUB_OUTPUT, each a JSON list for a job matrix:
  tlc=[...]     modules whose row list runs (rows/<Module>-rows.txt)
  proofs=[...]  modules whose proof runs (specs/<Module>_proof.tla)

A module is chosen when any of its inputs changed: a repository module in
its EXTENDS chain, its row list or its committed results, the generator
and comparison scripts, the pins, or the workflow. A TLC row list takes up
to two hours on a 2-CPU runner, so a change runs only what it can affect;
--all (a manual run, or a push with no earlier commit) runs everything.
"""
import glob
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tlc_rows import ROOT, SPECS, extends_chain  # noqa: E402

COMMON = {".github/workflows/checks.yml", "tools/TLA-KIT-PIN", "tools/check-kit-pin.sh",
          "scripts/compare_results.py", "scripts/tlc_rows.py"}
TLC = COMMON | {"tools/TLC-PIN"}
PROOF = COMMON | {"scripts/proof_results.py", "tools/tlapm", "tools/TLAPS-PIN"}


def main(argv):
    everything = "--all" in argv
    changed = set() if everything else {l.strip() for l in sys.stdin if l.strip()}
    tlc, proofs = [], []
    for rows in sorted(glob.glob(os.path.join(ROOT, "rows", "*-rows.txt"))):
        m = os.path.basename(rows)[:-len("-rows.txt")]
        inputs = TLC | {f"specs/{x}.tla" for x in extends_chain(m)} | {f"rows/{m}-rows.txt"}
        if everything or changed & inputs or any(c.startswith(f"results/{m}-results-") for c in changed):
            tlc.append(m)
    for proof in sorted(glob.glob(os.path.join(SPECS, "*_proof.tla"))):
        m = os.path.basename(proof)[:-len("_proof.tla")]
        inputs = PROOF | {f"specs/{x}.tla" for x in extends_chain(f"{m}_proof")}
        if everything or changed & inputs or any(c.startswith(f"results/{m}-proof-results-") for c in changed):
            proofs.append(m)
    print(f"tlc={json.dumps(tlc)}")
    print(f"proofs={json.dumps(proofs)}")


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
