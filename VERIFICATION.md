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
| `demo.py` | `6f10e91fca537a2573d8d7bc6b9e9817e4c3015affbb13fbee0d3481933eb954` |
| `moments.py` | `a62b7d3d945cfdc105d27523c36aedb123dea90b3237be6546881de1e9296fc5` |
| `verification_record.py` | `47b866bd15fd4092583bdd5d639f6d40295b13021f6473a4bf0eff9ae659c8f9` |
| `verify.py` | `10cf06685afb42f07c54f94638090517a97308f6ddaac685957d7d2da32aed00` |
| `main.tex` | `22c8bf203330095ca97ca71e48af33c02cf0a0b25014dbc2924c0608db93b161` |
| `uv.lock` | `f42a551741c991c958b95dde385de3818b2deb73de4f57397b4b0bcb53a44b92` |
| `pyproject.toml` | `5037da18f6503bba751fcd717bc43d056e94e475281cc562d8aaecaa20eb704a` |
| `.python-version` | `aa0d6581054e6e4ff3f91839deca7a854ad37221b8784d060b42d0f847ff1a3b` |
| `reproduce.sh` | `60481b912ab3d7055b60f10e2865e5c3fdc98ad397ad86a8af9a6d69a6c7fcd3` |
| `figures/ap.pdf` | `4def71088ca8c121d41cc3d8565c4637f5e925ce59b0df5c2171e929931ee2cd` |
| `lean/ap_distribution.lean` | `b11206560095cb6a81457bf094c376eb7a2e31010fa5209da7fb0d4b8a5772a7` |
| `lean/ap_moments.lean` | `cc22f747442d73397c234695290116adea807dcb23e31a6dbb1a2aa25fac980f` |
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
