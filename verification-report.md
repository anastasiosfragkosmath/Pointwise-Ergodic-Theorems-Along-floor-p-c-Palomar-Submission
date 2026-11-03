# Verification report

The paper-facing declarations are in [FractionalPrimes/PaperTheorems.lean](FractionalPrimes/PaperTheorems.lean). The [semantic audit](semantic-audit.md) records their correspondence with the paper and the author's selection of the pointwise prime-convergence conclusion.

## Local Lean checks

The full local Lean 4.35.0 build passed 12,981 jobs. The six core/submission declarations and three paper-facing declarations were audited explicitly; each depends only on `propext`, `Classical.choice`, and `Quot.sound`.

Canonical theorem types agree between Solution, the actual Challenge, and the independent statement review. Ten supporting definition dumps also agree. The source, layout, Challenge, and attribution checks passed. The independent Challenge contains exactly the three author-approved statement-only placeholders; the completed proof sources contain none.

Current evidence is recorded in `audits/build.json`, `audits/headline_axioms.json`, `audits/final_statement_comparison.json`, and `audits/attribution_checkpoint.json`.

## Independent-kernel verification

On 2026-10-31, the pre-cleanup a.e. Challenge/Solution snapshot passed sandboxed Comparator in the author's Ubuntu ARM64 VM:

- Con-ron accepted 142443 declarations with `--verified`.
- NanoDa accepted the solution.
- Lean's default kernel accepted the solution.
- Comparator printed `Your solution is okay!`; the author reported immediate pipeline exit status `0`.

The complete log and transferred reports were independently inspected. There are no error lines. All 3,933 Lean-source hashes and the recorded configuration hashes matched that historical source package checked locally. They do not describe the later cleaned or documented Challenge files. The precheck build passed 12,976 jobs; the sandbox Challenge and Solution builds passed 2,711 and 12,974 jobs respectively.

The accepted archive SHA256 is `51af466e88fa6113c5b4963a7575595405d2f9af5d6513e9e18c83103e17b2a7`. Its Lean-source manifest is `4192a1c99e425f6cbaa683cb60d55a6d64069b22e8d061bfd53651672bc1df9d`. The complete log has 3,177,318 bytes and 47,653 lines; its SHA256 is `80f44194ce6e32eba31b39164f7ad6a2827f0208e323b974f9f869f99f24b5d8`.

[audits/linux_comparator.json](audits/linux_comparator.json) binds the result to that snapshot and the copied Linux reports. The independent-kernel run checks the three configured submission theorems. The paper-facing declarations have the separate local Lean and axiom checks described above. Later removal of unused Challenge definitions and subsequent documentation changes altered the statement-file bytes. The compared claims and verification configuration remain unchanged; independent-kernel acceptance has not been established for those later snapshots. Registry and editorial acceptance remain separate.

## Reproduce local checks

```sh
lake exe cache get
lake build
lake build FractionalPrimes.PaperTheorems
python3 scripts/audit_sources.py --allow-challenge-placeholders
python3 scripts/audit_layout.py
python3 scripts/audit_challenge.py
python3 scripts/audit_axioms.py --already-built
python3 scripts/audit_attribution.py
```

The strict source scan rejects the three approved Challenge placeholders. The explicit exception permits those three alone. The axiom command requires a successful build of the same unchanged sources.

## Reproduce Comparator

Use Linux with at least 14 GiB RAM, 20 GiB free workspace disk, and a working bubblewrap sandbox. Install Git, Python 3, curl, bubblewrap, and the pinned Lean toolchain. From the repository root, run:

```sh
bash -o pipefail -c 'bash scripts/verify-comparator.sh 2>&1 | tee comparator-verification.log'
echo $?
```

Retain the complete log, immediate exit status, source commit identifier, and toolchain version. The configuration compares:

- `FractionalPrimes.Final.Palomar.primePowerVariation`
- `FractionalPrimes.Final.Palomar.primeAverageConvergence`
- `FractionalPrimes.Final.Palomar.mobiusAverageTendsToZero`

## Statement-file cleanup verification

On 2026-11-01, unused invertible-system definitions were removed from Challenge.lean and FinalChallengeStatements.lean. The three compared theorem statements and every retained supporting definition are unchanged. The full local `lake build` passed 12,981 jobs; source-policy, module-layout and Challenge-import checks passed. The cleaned Challenge has 166 lines and 6,337 bytes. See `audits/challenge_cleanup.json` for the checked snapshot.

The Ubuntu independent-kernel evidence above records the pre-cleanup Challenge file. GitHub Actions run [41359370486](https://github.com/anastasiosfragkosmath/Pointwise-Ergodic-Theorems-Along-floor-p-c-Palomar-Submission/actions/runs/41359370486) subsequently passed both the full build and the paper-facing build at commit `a96cc1d34108fe4dab121521ff2ecb766481e4d9`. On 2026-11-03, explanatory comments and docstrings were added to the statement files without changing Lean code. A fresh sandbox Comparator run of the current files remains pending. A successful `lake build` is distinct from Comparator verification.

## Policy documentation verification

On 2026-11-03, related-formalisation entries were added to both metadata files, the verification snapshot wording was clarified, and explanatory comments and docstrings were added to both statement files. All non-comment Lean code is unchanged. The full local build passed 12,981 jobs; the source-policy, layout, Challenge-import and six-declaration axiom checks passed. The documented Challenge has 183 lines and 7,639 bytes. Both YAML metadata files parse and agree. See `audits/policy_documentation_checkpoint.json`. No fresh Comparator acceptance is claimed.
