"""Build the current species and internodon papers and their navigation entries."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
DOCUMENTS = {
    "06-founding-cohort-species": "founding-cohort-species",
    "08-internodon-order-robustness": "internodon-order-robustness",
    "10-species-equivalence-and-iap-completeness": "species-equivalence-and-iap-completeness",
    "11-bounded-founders": "bounded-founders",
}


def run(command, cwd):
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    if result.returncode:
        raise SystemExit("\n".join((result.stdout + result.stderr).splitlines()[-40:]))
    return result.stdout + result.stderr


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(folder, allow_downloads):
    here = ROOT / folder
    stem = DOCUMENTS[folder]
    source = here / (stem + ".md")
    with tempfile.TemporaryDirectory(prefix="alexander-explanatory-") as work:
        work = Path(work)
        if (here / "figures").is_dir():
            shutil.copytree(here / "figures", work / "figures")
        template = run(["pandoc", "--print-default-data-file=templates/default.latex"], here)
        slot = "$fonts.latex()$"
        if template.count(slot) != 1:
            raise SystemExit("Cannot locate the Pandoc font partial")
        template = template.replace(slot, (ROOT / "explanatory-fonts.tex").read_text())
        (work / "template.latex").write_text(template)
        tex = work / (stem + ".tex")
        run([
            "pandoc", str(source), "--from=markdown+tex_math_single_backslash",
            "--to=latex", "--standalone", "--ascii",
            "--template", str(work / "template.latex"),
            "--lua-filter", str(ROOT / "explanatory-format.lua"),
            "--include-in-header", str(ROOT / "explanatory-header.tex"),
            "--variable=fontsize:11pt", "--variable=papersize:letter",
            "--variable=geometry:margin=1in", "--variable=colorlinks:true",
            "--variable=urlcolor:blue", "--output", str(tex),
        ], here)
        command = ["tectonic", "--keep-logs", "--outdir", str(work)]
        if not allow_downloads:
            command.append("--only-cached")
        run([*command, str(tex)], here)
        log = tex.with_suffix(".log").read_text(errors="replace")
        diagnostics = re.findall(r"^.*(?:Missing character:|undefined|multiply defined|Overfull).*$", log, re.M)
        if diagnostics:
            raise SystemExit("PDF diagnostics:\n" + "\n".join(diagnostics))
        pdf = tex.with_suffix(".pdf")
        text = run(["pdftotext", "-layout", str(pdf), "-"], here)
        endings = source.read_text().count(r"\(\square\)")
        if text.count("□") != endings:
            raise SystemExit(f"Proof-ending mismatch in {folder}")
        font_rows = run(["pdffonts", str(pdf)], here).splitlines()[2:]
        fonts = [row.split()[0].split("+")[-1] for row in font_rows]
        if not any(font.startswith("CMR") for font in fonts):
            raise SystemExit("Computer Modern Roman was not embedded")
        if any("DejaVu" in font or "LMRoman" in font for font in fonts):
            raise SystemExit("Unexpected font fallback")
        if not all(row.split()[-5] == "yes" for row in font_rows):
            raise SystemExit("A PDF font is not embedded")
        out_tex, out_pdf = here / tex.name, here / pdf.name
        out_tex.write_bytes(tex.read_bytes())
        out_pdf.write_bytes(pdf.read_bytes())
        info = run(["pdfinfo", str(out_pdf)], here)
        report = {
            "built_at_utc": datetime.now(timezone.utc).isoformat(),
            "source": source.name,
            "source_sha256": sha(source),
            "tex_sha256": sha(out_tex),
            "pdf_sha256": sha(out_pdf),
            "pages": int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1)),
            "proof_endings_source": endings,
            "proof_endings_pdf": text.count("□"),
            "embedded_fonts": fonts,
            "diagnostics": diagnostics,
            "network_resources_allowed": allow_downloads,
            "pandoc": run(["pandoc", "--version"], here).splitlines()[0],
            "tectonic": run(["tectonic", "--version"], here).strip(),
            "scope": "Document checks; no independent mathematical verification.",
        }
        (here / "pdf-build-report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(folder, report["pages"], "pages;", endings, "visible proof endings")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--allow-downloads", action="store_true")
    parser.add_argument("folders", nargs="*", default=list(DOCUMENTS), choices=list(DOCUMENTS))
    args = parser.parse_args()
    for folder in args.folders:
        build(folder, args.allow_downloads)
