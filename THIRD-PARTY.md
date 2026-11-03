# Third-party source and license attribution

The submission incorporates substantial pre-existing proof code. Original
copyright, author and license notices are retained. Each of the 2,945 bundled
or adapted third-party Lean files carries a prominent modification notice.
The maintainer does not claim sole authorship of these sources.

| Project | Exact revision | Included material | License copy |
| --- | --- | --- | --- |
| [OpenAI mathematics](https://github.com/openai/math) | `adc7f1241b42e322a6451854ab7e4b4c146bf78a` | 2,924 files in `OAI/NumberTheory/` | [Apache-2.0](third-party-licenses/LICENSE) |
| [Prime Number Theorem and More](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | `c39a751132c88b6e8080b74c74023fd95b3d8be0` | Four files under `PrimeNumberTheoremAnd/` | [Apache-2.0](third-party-licenses/PNT-LICENSE) |
| [Rellich–Kondrachov](https://github.com/abenenson/rellich-kondrachov) | `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23` | Fifteen files under `RellichKondrachov/` | [Apache-2.0](third-party-licenses/RELLICH-LICENSE) |
| [lean-spherical](https://github.com/roos-j/lean-spherical) | `f0dde64dcef87118c1d1dc9253e039da8f3f0482` | Schur-test and real-line translation portions adapted in `FractionalPrimes/Literature/JSW/SchurKernel.lean` and `SmoothL1Translation.lean` | [Apache-2.0](FractionalPrimes/Literature/JSW/LeanSpherical-LICENSE.txt) |
| [RiemannGaussian](https://github.com/dbsanfte/RiemannGaussian) | `07968f5ea0bff8caf39973599280e6321211c682` | Recorded source-preparation vendor snapshot; underlying sources credited separately above | [Apache-2.0](third-party-licenses/RIEMANN-GAUSSIAN-LICENSE) |

Lean 4.35.0 and [Mathlib](https://github.com/leanprover-community/mathlib4) at
`56a005855ea17e0b0958f73ec801ae140b0a1679`, together with the other exact
Lake dependencies in `lake-manifest.json`, are fetched separately at build time.
This archive does not contain `.lake`, Lean binaries or dependency caches.
Their own licenses/notices remain applicable if those artifacts are distributed.

## Modifications and retained notices

The 2,943-file source closure was converted to Lean modules/public imports;
selected files also received compatibility, visibility, proof/API or integration
changes. Details of those earlier changes are in the historical
[audits/provenance.json](audits/provenance.json). Its hashes describe the earlier
snapshot, not the newly annotated bytes. The current
[audits/attribution.json](audits/attribution.json) links every source to its
original repository/path, original and pre-notice hashes, current hash, license,
retained notice blocks, and exact added/replaced comment prefix. The two
lean-spherical adapters retain the original copyright, author and generation
notices and describe the adapted portions.

The pinned upstream source/license and applicable NOTICE inventories were checked.
All selected original author/copyright/license comment blocks were retained.
No separate upstream NOTICE file was found in the selected distributions or
source-preparation subtree. Unrelated RiemannGaussian subprojects with their own
NOTICE files are not included. The separately captured
[SiegelZeros support notices](PrimeNumberTheoremAnd/SiegelZeros/NOTICE.md) remain
included and are identified separately from the pinned PNT sources.

The project-authored [NOTICE](NOTICE) consolidates these credits; it is not an
assertion that upstream supplied that file. Preserve it, the license texts and
all original source notices when distributing this package. License conditions
are in the original license texts; these notes do not alter them or give legal
clearance.

## Citation and AI assistance

[CITATIONS.bib](CITATIONS.bib) gives repository/version references; the PNT
project's [preferred citation metadata](third-party-licenses/PNT-CITATION.cff)
is preserved verbatim. [ACKNOWLEDGMENTS.md](ACKNOWLEDGMENTS.md) credits reused developments; automation
details are recorded in formalization.yaml. No upstream endorsement is implied.

Reproduce the offline inventory, retained-notice, license-hash and comment-only
change checks with:

```sh
python3 scripts/audit_attribution.py
```

## Historical preparation and verification record

The package includes a source closure from the OpenAI mathematics repository at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, with upstream dependencies Rellich–Kondrachov at `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23` and PrimeNumberTheoremAnd at `c39a751132c88b6e8080b74c74023fd95b3d8be0`. The source preparation record also identifies `dbsanfte/RiemannGaussian` at `07968f5ea0bff8caf39973599280e6321211c682`. Their respective URLs, original compatibility patch hashes, and the original Mathlib pin appear in `audits/provenance.json`. The portable package instead pins Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` for Lean 4.35.0.

The included license texts are `third-party-licenses/LICENSE`, `third-party-licenses/PNT-LICENSE`, and `third-party-licenses/RELLICH-LICENSE`; each is Apache-2.0. Retain source-file copyright and license notices along with these texts.

The sources were moduleized and received compatibility and integration changes. The file-level record gives package and recorded upstream or baseline hashes and the integration change classifications. A match to the moduleization snapshot does not mean a file is unchanged from upstream: that snapshot includes the conversion and compatibility work. The integration record identifies 19 changes relative to the local moduleized baseline, including proof and API adjustments. The earlier verification and prototype snapshots differ by 24 bytes: three `private ` modifiers were removed in two files. Both historical source-tree hashes were independently reconstructed; see `audits/provenance_reconciliation.json`.

Historical staging and baseline portable builds passed 12,946 and 12,947 jobs, respectively, and the corrected baseline passed Linux sandbox Comparator. Those results certify the original manuscript snapshot only. The revised manuscript's current Lean build and six-declaration audit are recorded in audits/build.json and audits/headline_axioms.json. The earlier proof/configuration snapshot passed Linux sandbox Comparator with Con-ron, NanoDa and Lean default kernel; see audits/linux_comparator.json. The current author-selected a.e. prime-convergence snapshot also passed Linux sandbox Comparator with all three configured kernels; current verification scope is recorded in verification-report.md. The added paper-specific adapters and proofs are recorded in audits/final_provenance.json.
