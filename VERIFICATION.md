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
| `verification_record.py` | `3cdf728ae01dabf2e675ea21d7b38176c8a39551e12b374cad7499902b0cd429` |
| `verify.py` | `10cf06685afb42f07c54f94638090517a97308f6ddaac685957d7d2da32aed00` |
| `README.md` | `b56b40085496cfb74bcc86a46a0cd93ee7774efc576ba1b0ec0222b3b295be64` |
| `SUBMISSION_REVIEW.md` | `d9fdb6a7e3dae6b29c8f8485db6b5b50a976b1cb94a74a9ed8b7578dbe38f9d0` |
| `.gitignore` | `c9bf0fd7a94f8279d6e46a966ddfb2d7fad58f33e59985967714a4872c11a01d` |
| `CITATION.cff` | `a642abb4086687b5f4c93b80cf98882828125da66461bb69eb7e1c6d8a1bf4f5` |
| `CITATION.bib` | `de54f20a6ac579e768b5c4497f33a2b44f241842d05e04bb6de6934d9720e6d3` |
| `main.tex` | `168c7a07f8e1dc952a15e6de29ef3b62f254484f68e39a938a0016efd14fa8c9` |
| `uv.lock` | `36b7b0ea0c81ed8003a5f7abcd0e8b76d5414e8a254705bfe761b1f6ace7ca07` |
| `pyproject.toml` | `cbc93ef6f54b214c56d37864b2edab491cdb03c45deb6e43ebec7306e071ec27` |
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
The harmonic expectation formula and written exchangeability derivation are in the [September 7, 2025 source](https://github.com/shntnu/expected_ap/blob/4efbcf57d0d28a158dcbbe52872847d8e21ba130/expected_ap.md), Theorem 1 and proof.
This recorded derivation predates the [November 4, 2025 preprint](https://arxiv.org/abs/2511.02571) of Manzhos, Ianevych, and Melnyk.
The complete Lean expectation proof is in [commit 8aade13](https://github.com/shntnu/expected_ap/commit/8aade13f2bbb641f8cc75065770d391e5f42c798), dated March 23, 2026.
The variance implementation and proof are in [commit 10433fc](https://github.com/shntnu/expected_ap/commit/10433fc53ec65bbbc3a337a50de26c9cdbb2f9ea) and [commit 4071dd5](https://github.com/shntnu/expected_ap/commit/4071dd5c12281744259caebede7099a8bb7d5f0b), both dated July 23, 2026.
The dates above are recorded Git author and committer dates; they identify source versions rather than independently certified dates of first public availability.
