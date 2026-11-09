#!/usr/bin/env python3
"""Report whether every results file is in step with the tree.

usage: scripts/proof_sync.py [--run]

For every base module (a .tla at the top level that is not a proof module):

  - TLC: the newest results/<M>-results-*.txt; each digest on its Modules:
    line is compared with the tree and the Checker: digest with
    tools/TLC-PIN. Prints IN SYNC, STALE: <what moved>, or MISSING.
  - Proof: if <M>_proof.tla exists, the newest
    results/<M>-proof-results-*.txt, compared the same way (its Modules:
    line names the proof module too) and its Prover: digest with
    tools/TLAPS-PIN. If there is no proof module, the reason recorded for
    it in PROOF-GAPS.txt (one line, `<Module>: <reason>`) is printed; a
    module with neither a proof nor a reason is a failure.

Exit non-zero on any STALE, MISSING or unpinned row, or an unexplained gap.
With --run, each stale proof is re-checked with tools/tlapm --cleanfp
--strict, so the output says whether the drift broke the proof or only the
digest; no results file is written (scripts/proof_results.py does that).
"""
import glob
import os
import re
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tlc_rows import ROOT, pin, sha256  # noqa: E402


def newest(pattern):
    files = sorted(glob.glob(os.path.join(ROOT, "results", pattern)))
    return files[-1] if files else None


def field(path, key):
    for line in open(path):
        if line.startswith(key + ":"):
            return line.split(":", 1)[1].strip()
    return ""


def check_modules(path):
    moved = []
    pairs = re.findall(r"(\S+\.tla) ([0-9a-f]{64})", field(path, "Modules"))
    if not pairs:
        return ["no Modules: line"]
    for name, digest in pairs:
        p = os.path.join(ROOT, name)
        if not os.path.exists(p):
            moved.append(f"{name} (gone)")
        elif sha256(p) != digest:
            moved.append(name)
    return moved


def gaps():
    path = os.path.join(ROOT, "PROOF-GAPS.txt")
    out = {}
    if os.path.exists(path):
        for line in open(path):
            if ":" in line and not line.startswith("#"):
                k, v = line.split(":", 1)
                out[k.strip()] = v.strip()
    return out


def main(argv):
    run = "--run" in argv
    bad = 0
    tlc_pin = pin("TLC-PIN", "jar_sha256")
    tlaps_pin = pin("TLAPS-PIN", "binary_sha256")
    reasons = gaps()
    bases = sorted(os.path.basename(p)[:-4] for p in glob.glob(os.path.join(ROOT, "*.tla"))
                   if not p.endswith("_proof.tla") and "_TTrace_" not in p)
    for m in bases:
        r = newest(f"{m}-results-*.txt")
        if not r:
            print(f"{m:14} TLC    MISSING: no results/{m}-results-*.txt"); bad += 1
        else:
            moved = check_modules(r)
            unpinned = tlc_pin not in field(r, "Checker")
            status = "IN SYNC" if not moved else "STALE: " + ", ".join(moved)
            if unpinned:
                status += "; checker is not the pin"
            bad += bool(moved or unpinned)
            print(f"{m:14} TLC    {status}  ({os.path.basename(r)})")
        proof = os.path.join(ROOT, f"{m}_proof.tla")
        if not os.path.exists(proof):
            if m in reasons:
                print(f"{m:14} PROOF  none: {reasons[m]}")
            else:
                print(f"{m:14} PROOF  none and no reason in PROOF-GAPS.txt"); bad += 1
            continue
        r = newest(f"{m}-proof-results-*.txt")
        if not r:
            print(f"{m:14} PROOF  MISSING: no results/{m}-proof-results-*.txt"); bad += 1
            continue
        moved = check_modules(r)
        unpinned = tlaps_pin not in field(r, "Prover")
        status = "IN SYNC" if not moved else "STALE: " + ", ".join(moved)
        if unpinned:
            status += "; prover is not the pin"
        bad += bool(moved or unpinned)
        print(f"{m:14} PROOF  {status}  ({os.path.basename(r)}; {field(r, 'Result')})")
        if moved and run:
            cache = tempfile.mkdtemp(prefix="tlapm_sync_")
            try:
                p = subprocess.run([os.path.join(ROOT, "tools", "tlapm"), "--cleanfp", "--strict",
                                    "--cache-dir", cache, f"{m}_proof.tla"],
                                   cwd=ROOT, capture_output=True, text=True)
            finally:
                shutil.rmtree(cache, ignore_errors=True)
            out = p.stdout + p.stderr
            mm = re.search(r"All \d+ obligations? proved|\d+/\d+ obligations? failed", out)
            print(f"{'':14}        re-run: {mm.group(0) if mm else 'no count'} (exit {p.returncode})")
    print("sync: " + ("OK" if not bad else f"{bad} problem(s)"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
