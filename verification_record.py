"""Validate the theorem audit and record the source that was actually checked."""

import hashlib
import json
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parent
log = (root / "build/lean.log").read_text()
axioms = [line for line in log.splitlines() if "depends on axioms:" in line]
assert len(axioms) == 8, "Expected eight theorem audits"
assert all(line.endswith("[propext, Classical.choice, Quot.sound]") for line in axioms)
assert "Build completed successfully" in log
assert "error:" not in log.lower()
lean_version = subprocess.check_output(
    ["lean", "--version"], cwd=root / "lean", text=True
).strip()
manifest = json.loads((root / "lean/lake-manifest.json").read_text())
files = (
    sorted(root.glob("*.py"))
    + [
        root / "main.tex",
        root / "uv.lock",
        root / "pyproject.toml",
        root / ".python-version",
        root / "reproduce.sh",
        root / "figures/ap.pdf",
    ]
    + sorted((root / "lean").glob("*.lean"))
    + [root / "lean/lean-toolchain", root / "lean/lake-manifest.json"]
)
text = "# Verification record\n\n"
text += "Generated after a successful build and theorem audit by `verification_record.py`.\n"
text += f"Toolchain: `{lean_version}`.\n\n"
text += "The three paper modules were built from this checkout.\nMathlib compiled dependencies may be reused from the pinned cache.\n"
text += "Eight named results have exactly the axiom dependencies `propext`, `Classical.choice`, and `Quot.sound`.\nNo audited theorem depends on `sorryAx` or `Lean.ofReduceBool`.\n"
text += "The asymptotics, Python implementation, and literature comparison are not Lean-certified.\n\n"
text += "## Audited results\n\n"
for line in axioms:
    name = line.split("'")[1]
    text += f"- `{name}`.\n"
text += "\nThe mean and general variance require L > 1 and M != 0; the second moment requires M != 0.\n"
text += "The atom representation covers rational atoms with M determined by the label vector.\n"
text += "PMF normalization requires M <= L.\nVariance boundary results cover M = 0, M = 1, and M = L > 0.\n"
text += "The exact types are emitted by `lake env lean verify.lean`.\n\n"
text += "## Source hashes\n\n| File | SHA-256 |\n| --- | --- |\n"
for path in files:
    text += f"| `{path.relative_to(root)}` | `{hashlib.sha256(path.read_bytes()).hexdigest()}` |\n"
text += "\n## Lean dependencies\n\n| Package | Revision |\n| --- | --- |\n"
for package in manifest["packages"]:
    text += f"| {package['name']} | `{package['rev']}` |\n"
text += "\n## Provenance\n\n"
text += "This focused branch retains the committed three-module proof chain from `a96320920e82901c7bb0d3ef45f5cbf1a0436ca2`.\n"
text += "It does not incorporate unrelated uncommitted distribution extensions from the exploratory checkout.\n"
text += "The original expectation formula and written derivation are in commit `4efbcf5` (September 7, 2025); the complete expectation proof is in `8aade13` (March 23, 2026).\n"
text += "The variance implementation and proof are in `10433fc` and `4071dd5` (July 23, 2026).\n"
text += "These are recorded development dates, not certified dates of first public availability or claims of worldwide priority.\n"
(root / "VERIFICATION.md").write_text(text)
print("Verified eight axiom reports; wrote VERIFICATION.md with source hashes.")
