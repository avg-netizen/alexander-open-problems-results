"""Typeset the unchanged revised proof using Pandoc and Tectonic."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent
STEM = "REVISED-3-1-3-PROOF"


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--allow-downloads", action="store_true")
    args = parser.parse_args()
    source = ROOT / f"{STEM}.md"
    with tempfile.TemporaryDirectory(prefix="revised-313-pdf-") as work:
        tex = Path(work) / f"{STEM}.tex"
        run([
            "pandoc", str(source), "--from=markdown+tex_math_single_backslash",
            "--to=latex", "--standalone", "--lua-filter=pdf-format.lua",
            "--include-in-header=pdf-header.tex", "--variable=fontsize:11pt",
            "--variable=papersize:letter", "--variable=geometry:margin=1in",
            "--variable=colorlinks:true", "--variable=urlcolor:blue",
            "--output", str(tex),
        ])
        command = ["tectonic", "--keep-logs", "--outdir", work]
        if not args.allow_downloads:
            command.append("--only-cached")
        run([*command, str(tex)])
        log = (Path(work) / f"{STEM}.log").read_text(errors="replace")
        errors = re.findall(r"^.*(?:Missing character:|undefined|multiply defined).*$", log, re.M)
        if errors:
            raise SystemExit("PDF diagnostics:\n" + "\n".join(errors))
        pdf = ROOT / f"{STEM}.pdf"
        pdf.write_bytes((Path(work) / pdf.name).read_bytes())
        (ROOT / f"{STEM}.tex").write_bytes(tex.read_bytes())
        info = run(["pdfinfo", str(pdf)])
        text = run(["pdftotext", "-layout", str(pdf), "-"])
        if not text.strip() or "??" in text:
            raise SystemExit("PDF text is empty or contains unresolved references")
        report = {
            "built_at_utc": datetime.now(timezone.utc).isoformat(),
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "pdf_sha256": hashlib.sha256(pdf.read_bytes()).hexdigest(),
            "pages": int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1)),
            "source_math_delimiters": "Pandoc markdown+tex_math_single_backslash",
            "pandoc": run(["pandoc", "--version"]).splitlines()[0],
            "tectonic": run(["tectonic", "--version"]).strip(),
            "overfull_boxes": re.findall(r"^Overfull.*$", log, re.M),
            "missing_glyphs_or_unresolved_references": errors,
            "scope": "Typesetting of the supplied prose proof; source text unchanged.",
        }
        (ROOT / "pdf-build-report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
