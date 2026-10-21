"""Build both canonical Markdown papers with Pandoc and Tectonic."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent
PAPERS = (
    ("successor-knowers-3-2-1", "A negative answer to Alexander's Open Problem 3.2.1"),
    ("supplemental/additional-results", "Supplement to the successor-chain paper"),
)


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    return result.stdout + result.stderr


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(stem, subtitle, allow_downloads):
    source = ROOT / (stem + ".md")
    with tempfile.TemporaryDirectory(prefix="successor-chain-paper-") as work:
        tex = Path(work) / (Path(stem).name + ".tex")
        # Keep Pandoc's layout while selecting classic CM text and math fonts.
        template = run(["pandoc", "--print-default-data-file=templates/default.latex"])
        font_slot = "$fonts.latex()$"
        if template.count(font_slot) != 1:
            raise SystemExit("Cannot locate Pandoc's font partial in the LaTeX template")
        template = template.replace(font_slot, (ROOT / "pdf-fonts.tex").read_text())
        template_path = Path(work) / "computer-modern.latex"
        template_path.write_text(template)
        run([
            "pandoc", str(source), "--from=markdown+tex_math_single_backslash",
            "--to=latex", "--standalone", "--lua-filter=pdf-format.lua",
            "--template", str(template_path),
            "--include-in-header=pdf-header.tex", "--variable=fontsize:11pt",
            "--variable=papersize:letter", "--variable=geometry:margin=1in",
            "--variable=colorlinks:true", "--variable=urlcolor:blue",
            "--metadata=subtitle:" + subtitle, "--output", str(tex),
        ])
        command = ["tectonic", "--keep-logs", "--outdir", work]
        if not allow_downloads:
            command.append("--only-cached")
        run([*command, str(tex)])
        log = tex.with_suffix(".log").read_text(errors="replace")
        errors = re.findall(
            r"^.*(?:Missing character:|undefined|multiply defined).*$", log, re.M
        )
        if errors:
            raise SystemExit("PDF diagnostics:\n" + "\n".join(errors))
        pdf = tex.with_suffix(".pdf")
        info = run(["pdfinfo", str(pdf)])
        font_rows = run(["pdffonts", str(pdf)]).splitlines()[2:]
        fonts = [row.split()[0].split("+")[-1] for row in font_rows]
        if not any(font.startswith("CMR") for font in fonts):
            raise SystemExit("PDF does not embed Computer Modern Roman")
        if any("DejaVu" in font or "LMRoman" in font for font in fonts):
            raise SystemExit("Unexpected font fallback in PDF")
        extracted = run(["pdftotext", "-layout", str(pdf), "-"])
        if not extracted.strip() or "??" in extracted:
            raise SystemExit("PDF text is empty or contains unresolved references")
        source_endings = source.read_text().count(r"\(\square\)")
        pdf_endings = extracted.count("□")
        if source_endings != pdf_endings:
            raise SystemExit(
                f"Proof ending mismatch for {stem}: {source_endings} vs {pdf_endings}"
            )
        output_tex = ROOT / (stem + ".tex")
        output_pdf = ROOT / (stem + ".pdf")
        output_tex.write_bytes(tex.read_bytes())
        output_pdf.write_bytes(pdf.read_bytes())
        return {
            "source": stem + ".md",
            "source_sha256": sha(source),
            "tex_sha256": sha(output_tex),
            "pdf_sha256": sha(output_pdf),
            "pages": int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1)),
            "embedded_fonts": fonts,
            "proof_endings_source": source_endings,
            "proof_endings_pdf": pdf_endings,
            "overfull_boxes": re.findall(r"^Overfull.*$", log, re.M),
            "missing_glyphs_or_unresolved_references": errors,
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--allow-downloads", action="store_true")
    args = parser.parse_args()
    reports = [build(stem, subtitle, args.allow_downloads) for stem, subtitle in PAPERS]
    report = {
        "built_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_math_delimiters": "Pandoc markdown+tex_math_single_backslash",
        "pandoc": run(["pandoc", "--version"]).splitlines()[0],
        "tectonic": run(["tectonic", "--version"]).strip(),
        "network_resources_allowed": args.allow_downloads,
        "font_family": "Computer Modern",
        "papers": reports,
        "scope": "Document generation and visible proof endings; no formal mathematical verification.",
    }
    (ROOT / "pdf-build-report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
