"""Build the canonical LaTeX manuscript with cached resources by default."""

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parent


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command):
    return subprocess.run(command, cwd=ROOT, text=True, capture_output=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--allow-downloads", action="store_true")
    args = parser.parse_args()
    source = (ROOT / "paper.tex").read_text()
    labels = re.findall(r"\\label\{([^}]+)\}", source)
    refs = re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", source)
    duplicates = [key for key, count in Counter(labels).items() if count > 1]
    missing = sorted(set(refs) - set(labels))
    if duplicates or missing:
        raise SystemExit(f"Bad LaTeX labels: duplicates={duplicates}; missing={missing}")
    command = ["tectonic", "--keep-logs"]
    if not args.allow_downloads:
        command.append("--only-cached")
    command.append("paper.tex")
    result = run(command)
    output = result.stdout + result.stderr
    font_diagnostics = [line for line in output.splitlines()
                        if line.startswith("warning: accessing absolute path")]
    concise_output = "\n".join(line for line in output.splitlines()
                              if line not in font_diagnostics)
    (ROOT / "build-output.txt").write_text(concise_output + "\n")
    if result.returncode:
        raise SystemExit(concise_output[-10000:])
    tex_log = (ROOT / "paper.log").read_text(errors="replace")
    unresolved = re.findall(r"^.*(?:undefined|multiply defined).*$", tex_log, re.M)
    if unresolved:
        raise SystemExit("Unresolved TeX references: " + "\n".join(unresolved))
    missing_glyphs = re.findall(r"^Missing character:.*$", tex_log, re.M)
    if missing_glyphs:
        raise SystemExit("Missing glyphs: " + "\n".join(missing_glyphs))
    pdf_info = run(["pdfinfo", "paper.pdf"])
    if pdf_info.returncode:
        raise SystemExit(pdf_info.stderr)
    pages = int(re.search(r"^Pages:\s+(\d+)", pdf_info.stdout, re.M).group(1))
    extracted = run(["pdftotext", "-layout", "paper.pdf", "-"])
    if extracted.returncode:
        raise SystemExit(extracted.stderr)
    if not extracted.stdout.strip() or "??" in extracted.stdout:
        raise SystemExit("Empty PDF text or unresolved reference marker in PDF")
    font_result = run(["pdffonts", "paper.pdf"])
    if font_result.returncode:
        raise SystemExit(font_result.stderr)
    fonts = []
    for line in font_result.stdout.splitlines()[2:]:
        fields = line.split()
        if fields:
            fonts.append({"name": fields[0], "embedded": fields[-5] == "yes"})
    if not fonts or not all(font["embedded"] for font in fonts):
        raise SystemExit("PDF fonts are absent or not all embedded")
    report = {
        "built_at_utc": datetime.now(timezone.utc).isoformat(),
        "command": command,
        "engine": run(["tectonic", "--version"]).stdout.strip(),
        "pages": pages,
        "pdf_text_words": len(extracted.stdout.split()),
        "latex_labels": len(labels),
        "missing_labels": missing,
        "duplicate_labels": duplicates,
        "unresolved_references_or_citations": unresolved,
        "missing_glyphs": missing_glyphs,
        "fonts": fonts,
        "overfull_boxes": re.findall(r"^Overfull.*$", tex_log, re.M),
        "underfull_boxes": re.findall(r"^Underfull.*$", tex_log, re.M),
        "engine_font_access_diagnostics": len(font_diagnostics),
        "artifacts": {name: {"sha256": sha256(ROOT / name),
                             "bytes": (ROOT / name).stat().st_size}
                      for name in ["paper.tex", "paper.pdf"]},
        "verification_scope": "Document build and cross-references only; no mathematical or Lean certification.",
    }
    (ROOT / "build-report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in
                      ["pages", "pdf_text_words", "latex_labels", "overfull_boxes",
                       "underfull_boxes", "unresolved_references_or_citations"]}, indent=2))


if __name__ == "__main__":
    main()
