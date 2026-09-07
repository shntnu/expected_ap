"""Package the current paper and supplement after reproduction, without Git."""

from io import BytesIO
from pathlib import Path
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

ROOT = Path(__file__).resolve().parent
SOURCES = [
    ".gitignore",
    ".python-version",
    "CITATION.cff",
    "CITATION.bib",
    "README.md",
    "SUBMISSION_REVIEW.md",
    "VERIFICATION.md",
    "demo.py",
    "figures/ap.pdf",
    "lean/ap_distribution.lean",
    "lean/ap_moments.lean",
    "lean/expected_ap.lean",
    "lean/lake-manifest.json",
    "lean/lakefile.lean",
    "lean/lean-toolchain",
    "lean/verify.lean",
    "main.tex",
    "moments.py",
    "package.py",
    "pyproject.toml",
    "reproduce.sh",
    "uv.lock",
    "verification_record.py",
    "verify.py",
]


def write_archive(path, sources):
    with ZipFile(path, "w", compression=ZIP_DEFLATED) as archive:
        for name, data in sources:
            info = ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
            info.compress_type = ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data)


def main():
    output = ROOT / "build"
    output.mkdir(exist_ok=True)
    sources = [(name, (ROOT / name).read_bytes()) for name in SOURCES]
    write_archive(output / "supplement.zip", sources)
    paper = {"main.tex", "figures/ap.pdf"}
    ancillary = BytesIO()
    write_archive(
        ancillary, [(name, data) for name, data in sources if name not in paper]
    )
    write_archive(
        output / "arxiv-source.zip",
        [(name, data) for name, data in sources if name in paper]
        + [("anc/supplement.zip", ancillary.getvalue())],
    )
    print("Wrote build/supplement.zip and build/arxiv-source.zip.")


if __name__ == "__main__":
    main()
