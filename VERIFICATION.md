# Verification record

Generated after a successful build and theorem audit by `verification_record.py`.
Toolchain: `Lean (version 4.23.0-rc2, arm64-apple-darwin23.6.0, commit ad1a017949674a947f0d6794cbf7130d642c6530, Release)`.

The three paper modules were built from this checkout.
Mathlib compiled dependencies may be reused from the pinned cache.
Eight named results have exactly the axiom dependencies `propext`, `Classical.choice`, and `Quot.sound`.
No audited theorem depends on `sorryAx` or `Lean.ofReduceBool`.
The asymptotics, Python implementation, and literature comparison are not Lean-certified.

## Audited results

- `ExpectedAp.expected_ap_closed_form`.
- `ExpectedAp.secondMomentAP_eq_expectedWSq_div`.
- `ExpectedAp.varianceAP_closed_form`.
- `ExpectedAp.uniformAPMass_closed_form_explicit`.
- `ExpectedAp.sum_apPMF_eq_one`.
- `ExpectedAp.varianceAP_closed_form_of_numRelevant_eq_zero`.
- `ExpectedAp.varianceAP_closed_form_of_numRelevant_eq_one`.
- `ExpectedAp.varianceAP_closed_form_of_numRelevant_eq_card`.

The mean and general variance require L > 1 and M != 0; the second moment requires M != 0.
The atom representation covers rational atoms with M determined by the label vector.
PMF normalization requires M <= L.
Variance boundary results cover M = 0, M = 1, and M = L > 0.
The exact types are emitted by `lake env lean verify.lean`.

## Source hashes

| File | SHA-256 |
| --- | --- |
| `demo.py` | `1eb7dc1a049871f8d31db81e68fb5afc3c3c1269863bce6e0c1d8feb52b7f074` |
| `moments.py` | `a8e21928517e70e11aefafeebe7c03498b714cde875449f3f99a13c18348694e` |
| `package.py` | `c88f5fe3dc855e39fc6298272bd481a01ef78eaf5da39d3815afd263d16ad736` |
| `verification_record.py` | `005314451430bc87c9515b26bcce71b72694a1b6814ccbcfb7ff5c3ef0488d35` |
| `verify.py` | `10cf06685afb42f07c54f94638090517a97308f6ddaac685957d7d2da32aed00` |
| `README.md` | `4340d00665bd32dbb637b41668b62528a7a761d7ef0125df0e53318f0c32666b` |
| `SUBMISSION_REVIEW.md` | `1c499397facb09391457b94c8110718f56a6eddda1eb5e00c1acc31873cb2c36` |
| `.gitignore` | `c9bf0fd7a94f8279d6e46a966ddfb2d7fad58f33e59985967714a4872c11a01d` |
| `CITATION.cff` | `17e85c61faddfb01fc9127719f63ceaac850c6accf140b6cb63524486e2d0795` |
| `CITATION.bib` | `024d22851917a32a9d2bb7880a1614f36aef3da1794da10f355c84145b0d4cf8` |
| `main.tex` | `c636a73c2ec41e168c09f524af26ea784e78f0d996a6f71badc3abb5ef556461` |
| `uv.lock` | `be03283262f4fcc9eab32bde9287ece2b3616880d989730c56a3f4d970459f96` |
| `pyproject.toml` | `d19050e606ac7210b69dc211d9c5ee0de14d316b0759b8ad4a15ca2a2a3816da` |
| `.python-version` | `aa0d6581054e6e4ff3f91839deca7a854ad37221b8784d060b42d0f847ff1a3b` |
| `reproduce.sh` | `85378fc990163a2268a3533bbeb4a64309ab06864b3c7c434500b905cab4c545` |
| `figures/ap.pdf` | `4def71088ca8c121d41cc3d8565c4637f5e925ce59b0df5c2171e929931ee2cd` |
| `lean/ap_distribution.lean` | `b11206560095cb6a81457bf094c376eb7a2e31010fa5209da7fb0d4b8a5772a7` |
| `lean/ap_moments.lean` | `bf327233de31e57d8602fee26cd58dbbb07d8c47c2fc6f57641eefe7802ec0de` |
| `lean/expected_ap.lean` | `c2f573ef467e24ce349a170f64c86ca8574d66ef448b88b9f5496d162c714c5e` |
| `lean/lakefile.lean` | `e0eafc4b6112dd345bd6becdc40afa2e3eab754f2550b7a2682f6fe6d0bd8c28` |
| `lean/verify.lean` | `c83521dff5b4e8d6807f0a4731b42fc306a9a0013b5c3205e5d766e739409df0` |
| `lean/lean-toolchain` | `410d5c912b1a040c79883f5e0bb55e733888534e2006eefe186e631c24864546` |
| `lean/lake-manifest.json` | `54a00afb6ddd5a82cbf529d38639b9bfa6bced66cd9c7593d6da49344d6907e2` |

## Lean dependencies

| Package | Revision |
| --- | --- |
| mathlib | `1437899b35b71d2988ae71596597bb94e1adf709` |
| plausible | `240eddc1bb31420fbbc57fe5cc579435c2522493` |
| LeanSearchClient | `99657ad92e23804e279f77ea6dbdeebaa1317b98` |
| importGraph | `dba7fbc707774d1ba830fd44d7f92a717e9bf57f` |
| proofwidgets | `6e47cc88cfbf1601ab364e9a4de5f33f13401ff8` |
| aesop | `3b779e9d1c73837a3764d516d81f942de391b6f0` |
| Qq | `f85ad59c9b60647ef736719c23edd4578f723806` |
| batteries | `a67fc66cd1ebc0855dc064a4be727798771c0f89` |
| Cli | `cacb481a1eaa4d7d4530a27b606c60923da21caf` |

## Provenance

This focused branch retains the committed three-module proof chain from `a96320920e82901c7bb0d3ef45f5cbf1a0436ca2`.
It does not incorporate unrelated uncommitted distribution extensions from the exploratory checkout.
The original expectation formula and written derivation are in commit `4efbcf5` (September 7, 2025); the complete expectation proof is in `8aade13` (March 23, 2026).
The variance implementation and proof are in `10433fc` and `4071dd5` (July 23, 2026).
These are recorded development dates, not certified dates of first public availability or claims of worldwide priority.
