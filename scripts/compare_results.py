#!/usr/bin/env python3
"""Compare a fresh results file with the newest committed one for its module.

usage: scripts/compare_results.py tlc   <Module> <fresh>
       scripts/compare_results.py proof <Module> <fresh> [--counts-only]

The committed file is the newest results/<Module>-results-*.txt (tlc) or
results/<Module>-proof-results-*.txt (proof). The fresh one is written by
scripts/tlc_rows.py or scripts/proof_results.py with --out.

Full comparison: every line must be equal, except the date in the header
(line 2 of a TLC results file, line 1 of a proof results file). The
generators are deterministic: rows run with -workers 1, a counterexample
row's count is not printed, so any other difference is real. Either the
committed file is stale (regenerate it as a new dated file, by hand) or the
checker behaves differently here (investigate).

--counts-only (proofs, while tools/TLAPS-PIN and the image name different
provers): compares the Modules: line, which says whether the committed file
describes the text in the tree, and the Result: line, the obligation count.
The Prover: and Backends: lines differ on purpose and are printed, not
compared.

Exit 0 when they agree, 1 with the differences listed otherwise.
"""
import difflib
import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATE = re.compile(r"\d{4}\.\d{2}\.\d{2}")


def newest(kind, module):
    pat = f"{module}-results-*.txt" if kind == "tlc" else f"{module}-proof-results-*.txt"
    # YYYY.MM.DD sorts by date, and a letter suffix after the file it follows.
    files = sorted(glob.glob(os.path.join(ROOT, "results", pat)))
    if not files:
        raise SystemExit(f"no committed results/{pat}")
    return files[-1]


def normalised(kind, lines):
    i = 1 if kind == "tlc" else 0
    return [DATE.sub("<date>", l, count=1) if n == i else l for n, l in enumerate(lines)]


def field(lines, name):
    return next((l for l in lines if l.startswith(name + ":")), f"(no {name}: line)")


def main(argv):
    counts_only = "--counts-only" in argv
    args = [a for a in argv if not a.startswith("--")]
    if len(args) != 3 or args[0] not in ("tlc", "proof"):
        print(__doc__)
        return 2
    kind, module, fresh = args
    committed = newest(kind, module)
    a = open(committed).read().splitlines()
    b = open(fresh).read().splitlines()
    rel = os.path.relpath(committed, ROOT)
    print(f"committed: {rel}\nfresh:     {fresh}")

    if counts_only:
        diffs = [(k, field(a, k), field(b, k)) for k in ("Modules", "Result") if field(a, k) != field(b, k)]
        for k in ("Prover", "Backends"):
            print(f"{k} (not compared):\n  committed: {field(a, k)}\n  fresh:     {field(b, k)}")
        for k, x, y in diffs:
            print(f"{k}: line differs:\n  committed: {x}\n  fresh:     {y}")
        if any(k == "Modules" for k, _, _ in diffs):
            print(f"{rel} does not describe the modules in the tree: it is stale (scripts/proof_sync.py).")
        print(f"{module} proof, counts only: {field(b, 'Result')} "
              + ("agrees" if not diffs else f"{len(diffs)} differences"))
        return 1 if diffs else 0

    diff = list(difflib.unified_diff(normalised(kind, a), normalised(kind, b),
                                     rel, fresh, lineterm="", n=0))
    print("\n".join(diff[:400]))
    if len(diff) > 400:
        print(f"... {len(diff) - 400} more diff lines")
    print(f"{module} {kind}: " + ("reproduced, but for the date" if not diff else "DIFFERS from the committed file"))
    return 1 if diff else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
