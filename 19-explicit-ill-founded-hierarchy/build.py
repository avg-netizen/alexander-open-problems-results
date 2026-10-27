"""Compile the standalone paper offline and record document checks."""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent
STEM = "ill-founded-hierarchy"


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    return result.stdout + result.stderr


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source = ROOT / (STEM + ".tex")
    with tempfile.TemporaryDirectory(prefix="ill-founded-paper-") as directory:
        work = Path(directory)
        run([
            "tectonic", "--only-cached", "--keep-logs", "--outdir", str(work),
            str(source),
        ])
        pdf = work / (STEM + ".pdf")
        log = (work / (STEM + ".log")).read_text(errors="replace")
        problems = re.findall(
            r"^.*(?:Missing character:|undefined|multiply defined).*$", log, re.M
        )
        if problems:
            raise SystemExit("Unresolved document diagnostics:\n" + "\n".join(problems))
        info = run(["pdfinfo", str(pdf)])
        fonts = [
            line.split()[0].split("+")[-1]
            for line in run(["pdffonts", str(pdf)]).splitlines()[2:]
        ]
        if not any(font.startswith("CMR") for font in fonts):
            raise SystemExit("Computer Modern Roman is not embedded")
        if any(not font.startswith(("CM", "MS")) for font in fonts):
            raise SystemExit("Unexpected font family: " + repr(fonts))
        text = run(["pdftotext", "-layout", str(pdf), "-"])
        if not text.strip() or "??" in text:
            raise SystemExit("PDF text is empty or has unresolved references")
        proof_count = source.read_text().count(r"\begin{proof}")
        endings = text.count("□")
        if proof_count != endings:
            raise SystemExit(f"Proof ending mismatch: {proof_count} versus {endings}")
        output = ROOT / (STEM + ".pdf")
        output.write_bytes(pdf.read_bytes())
        report = {
            "built_at_utc": datetime.now(timezone.utc).isoformat(),
            "source": source.name,
            "source_sha256": digest(source),
            "pdf": output.name,
            "pdf_sha256": digest(output),
            "pages": int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1)),
            "font_family": "Computer Modern",
            "embedded_fonts": fonts,
            "proofs_in_source": proof_count,
            "visible_proof_endings": endings,
            "missing_glyphs_or_unresolved_references": problems,
            "overfull_boxes": re.findall(r"^Overfull.*$", log, re.M),
            "network_resources_allowed": False,
            "tectonic": run(["tectonic", "--version"]).strip(),
            "scope": "Document compilation and text/font checks; not formal mathematical verification.",
        }
        (ROOT / "pdf-build-report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
