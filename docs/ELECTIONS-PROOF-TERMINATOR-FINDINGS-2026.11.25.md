# Twenty-four lemmas after the end of Elections_proof.tla: how drawing found them, and the fix

> `specs/Elections_proof.tla` ended at line 1372. The 24 `Mut…Admits` lemmas
> below that line were in the file but not in the module, so the prover never
> saw them, and the results file listed them anyway.

**2026.11.25** · findings and fix · found while drawing the gov-tla diagram
family (PR #15); fixed on branch `fix-elections-proof-terminator` by deleting
one line and re-proving in the pinned tla-kit image · prepared by Claude at
the maintainer's request · read against commit `d3c9aed` on `main`:
`specs/Elections_proof.tla` (sha256 `d62cd23fc210…`, the digest that
`results/Elections-proof-results-2026.11.17.txt` cites)

---

## 1. Summary

- **The defect.** `specs/Elections_proof.tla` had two module terminators
  (`====` lines): one at line 1372, after `ExecutiveIsFilledAlways`, and one at
  line 1525, at the end of the file. A TLA+ module ends at its first
  terminator, and the tools ignore whatever follows. The 24 lemmas
  `MutOfficerElectorAdmits` … (lines 1379–1523), one per mutation, came after
  the first.
- **What it meant.** The 24 lemmas were never checked. The 2026.11.17 results
  file says "All 1121 obligations proved", and that count is right for the
  module tlapm read. But the file's `LEMMAS (71)` line also names the 24,
  because `scripts/proof_results.py` reads statement names from the whole
  file. So the evidence appeared to cover statements the prover never saw.
- **What it did not affect.** No theorem cites any of the 24 lemmas, so every
  theorem the results file lists was proved as stated: the nineteen safety
  properties, `ExecutiveIsFilled` and `SafeAlways`. The other eleven modules,
  base and proof, each have exactly one terminator, at their last line.
- **The fix.** Delete the first terminator. Re-proved with the pinned prover
  in the pinned image: **all 1,145 obligations proved**, which is the 1,121
  before plus one per lemma. The new results file is
  `results/Elections-proof-results-2026.11.26.txt`, and the README's summary
  table now reads 1,145.

## 2. The defect

Both terminators were in the file from its first commit, `373c3f5`
(2026-11-17, "Prove Elections.tla: nineteen safety properties and
ExecutiveIsFilled"). As committed:

```
1370  <1> QED
1371    BY <1>1, <1>2, <1>3, PTL DEF FairSpec, Spec, SomeoneActs, ExecutiveIsFilled
1372  ========================================================================
1373
1374  -----------------------------------------------------------------------------
1375  (* Why each mutation must fail: what it admits, in the module's terms. The  *)
1376  (* counterexamples are TLC's (results/Elections-results-*.txt).             *)
1377
1378  \* An officer of the United States may be appointed an elector.
1379  LEMMA MutOfficerElectorAdmits ==
  …
1520  LEMMA MutNoStatuteAdmits ==   (the last of the 24, ending at 1523)
  …
1525  =============================================================================
```

The lemmas were written, and they are the shape the method prescribes: each
says, in the module's vocabulary, what its mutation admits, so that the
counterexample TLC finds has a stated reason to exist (README § How the specs
are written and checked: "one lemma per mutation saying what that mutation
admits"). They were simply outside the module.

## 3. Why nothing caught it

Every check in the repository passed, because each one compares the files with
each other, and the files agreed with each other:

| Check | Why it passed |
|---|---|
| `tools/tlapm --cleanfp --strict` | Text after the terminator is not part of the module, and tlapm does not report it. It proved every obligation of the module it read and exited 0. |
| `scripts/proof_results.py` | It writes the file only if the prover proves everything, and it did. Its `statements()` scans the whole file text for `LEMMA` names, so the `LEMMAS` line listed all 71, including the 24 the prover never read. Nothing compares that list with the obligation count. |
| `scripts/proof_sync.py` | It compares digests: the results file cited the module as it stood. IN SYNC. |
| CI (`scripts/compare_results.py`) | It reproduces the results file and compares it line for line with the committed one. Both runs read the same module, so both say 1,121. |
| `scripts/flip_test.py` | It flips the `Mut # "M_X"` hypotheses of theorems. The 24 lemmas assume `Mut = "M_X"` and carry no such hypothesis, so no flip touches them. |
| Review and the README | The README describes the method in general ("one lemma per mutation"). It gives no per-module lemma count to compare. |

So the one number that could have shown the gap, the obligation count, was
correct for what was proved. The list that looked like coverage came from a
different reading of the file than the prover's.

## 4. How it was found

The gov-tla diagram family (PR #15) was drawn with TOPAK's
`generating-corpus-diagrams` skill: one diagram per module, each drawn by an
agent that reads its module's records in full, with counts and verdicts read
from the results files when the diagram is built. The skill's premise is that
drawing is a strict second reading: a generator that must place every theorem
and lemma beside its source shows where the records and the evidence part.

The agent drawing B5 (`Elections.tla`) had to draw the proofs band: each
`THEOREM` with its hypotheses, read from the proof results file, beside the
proof module. Its report listed this first among its findings:
"`specs/Elections_proof.tla:1372` is a `====` line that ends the module after
`ExecutiveIsFilledAlways`. All 24 `Mut…Admits` lemmas (lines 1379–1520) come
after it … `scripts/proof_results.py` `statements()` reads LEMMA names from the
whole text, so the results file lists all 71. No record says whether tlapm
checked those 24."

Under the skill's rule that an agent's report is a lead until checked against
the files, it was checked. The report held, except for one detail: the last
lemma ends at line 1523, not 1520.

- `grep -n -E '^={4,}\s*$'` over all twelve modules in `specs/`: only
  `Elections_proof.tla` has two terminators. Every other module has one, at its
  last line.
- No line of the proof module outside its own definition names any of the 24
  lemmas, so no proof could have depended on them.
- `git blame`: both terminators date from `373c3f5`.

B5 drew the 24 lemmas in red, as "after the first end-of-module line", and the
family's findings file (`diagrams/FINDINGS-2026.11.25.md`, item 1) recorded
it. At that point, whether the lemmas would prove was not known: they had never
been run.

## 5. The fix

**The change.** One line deleted, the first terminator, and the blank line
after it:

```diff
   BY <1>1, <1>2, <1>3, PTL DEF FairSpec, Spec, SomeoneActs, ExecutiveIsFilled
-========================================================================
 
 -----------------------------------------------------------------------------
 (* Why each mutation must fail: what it admits, in the module's terms. The  *)
```

The module now ends at line 1524. Nothing else in it changed, and
`specs/Elections.tla` is untouched.

The `writing-tla-specs-and-proofs` skill would freeze a module that evidence
cites by digest and change it only as a successor. This repository edits
modules in place and records each change as a new dated results file (README
§ How the specs are written and checked, on where the README and the skill
differ), and the fix follows that practice.

**The proof.** The pinned prover (`tools/TLAPS-PIN`: tlapm 1.6.0-pre, commit
`ff40755`) is a Linux x86_64 build, so it was run as CI runs it, in the
tla-kit image named by `tools/TLA-KIT-PIN`:

1. `tools/check-kit-pin.sh`: the image's provenance attestation verified
   against `scottcochran/tla-kit`, and its jar and tlapm are the pinned ones.
2. `docker run --rm --platform linux/amd64 -v "$PWD:/work" -w /work "$IMAGE"
   python3 scripts/proof_results.py Elections --threads 8`.
3. Result: **"All 1145 obligations proved."** It took 51 seconds, under amd64
   emulation on an arm64 Mac.

The script wrote `results/Elections-proof-results-2026.11.26.txt`. It is dated
the 26th because the container's clock is UTC, past midnight. Results files are
never edited, so the name stands. Against the 2026.11.17 file, three lines
differ, and only these:

| Line | 2026.11.17 | 2026.11.26 |
|---|---|---|
| 1 | `… TLAPS proof results 2026.11.17` | `… TLAPS proof results 2026.11.26` |
| 3 | `Elections_proof.tla d62cd23fc210…` | `Elections_proof.tla 4f5107816d73…` |
| 34 | `Result: All 1121 obligations proved.` | `Result: All 1145 obligations proved.` |

The theorem and lemma lists are identical, because the script listed the 24
all along. The difference of exactly 24 means each lemma took one obligation.
Each is a one-step `BY DEF` of the operator its mutation changes.

**The rest.**

- `README.md`'s summary table: `Elections.tla` obligations 1,121 → 1,145.
  The README states the count nowhere else.
- `python3 scripts/proof_sync.py`: every TLC and proof results file IN SYNC,
  `sync: OK`.
- The flip tests were not re-run. No theorem and no hypothesis changed, and
  the 24 lemmas carry no `Mut #` hypothesis to flip.
- `docs/MUTATION-MATRIX-FINDINGS-2026.11.17.md` § 7.6 says "1,121
  obligations". It is a dated record of the 2026.11.17 run and was right
  about that run, so it is left as written.

## 6. What it means now

- Every lemma `Elections_proof.tla` states is now in the module and proved,
  and the README's description of the proof modules ("one lemma per mutation
  saying what that mutation admits") holds of Elections.
- No earlier claim is withdrawn. The theorems proved on 2026.11.17 are the same
  theorems, proved again in the same run.
- The 2026.11.17 results file stays in `results/`, as every superseded results
  file does. Its `LEMMAS (71)` line overstated what it covered. Its obligation
  count did not.

## 7. Not done, and worth doing

1. **Make `scripts/proof_results.py` refuse the shape.** Its `statements()`
   could read only up to the module's first terminator. Or the script could
   exit non-zero when a `THEOREM` or `LEMMA` follows the first `====` line.
   Either would have stopped the 2026.11.17 file being written. A check that
   every base and proof module has exactly one terminator, at its last
   non-blank line, would belong in `scripts/proof_sync.py`.
2. **Upstream to the skill.** `writing-tla-specs-and-proofs` could add the rule
   to its anti-patterns: one terminator per module, and a results generator
   that reads statements from the module as the prover parses it, not from the
   file text.

**Done in the same pull request: the diagram amendment.** Once this branch
was rebased onto the merged diagram family, A1, the family's gate, refused to
build. The new results file was the newest of its kind, and
`diagrams/gov-tla/src/corpus.py` did not name it. That is the gate working.
`corpus.RESULTS` now names the 2026.11.26 file, and A1 and B5 are amended
against `a6e724e`, the commit of the fix: their footers say so, and their links
out open that commit. B5 draws the 24 lemmas inside the module and proved.
Item 1 of `diagrams/FINDINGS-2026.11.25.md` is marked fixed. The other five
diagrams read nothing that changed and regenerate byte for byte.

## Appendix A. Reproducing

```bash
# The defect, on main at d3c9aed: two terminators, only in this module
for f in specs/*.tla; do echo "$f $(grep -c -E '^={4,}\s*$' "$f")"; done

# The fix's proof, as CI runs it
IMAGE=$(tools/check-kit-pin.sh | tail -1)
docker run --rm --platform linux/amd64 -v "$PWD:/work" -w /work "$IMAGE" \
  python3 scripts/proof_results.py Elections --threads 8
diff results/Elections-proof-results-2026.11.17.txt results/Elections-proof-results-2026.11.26.txt
python3 scripts/proof_sync.py
```
