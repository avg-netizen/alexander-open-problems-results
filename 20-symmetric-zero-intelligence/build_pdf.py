#!/usr/bin/env python3
"""Build this standalone manuscript with a standard pdfLaTeX installation."""
from pathlib import Path
import re
import shutil
import subprocess

directory = Path(__file__).resolve().parent
for command in (["pdflatex", "bibtex"] if (directory / "references.bib").exists() else ["pdflatex"]):
    if not shutil.which(command):
        raise SystemExit(f"{command} is required; install a standard TeX Live or MiKTeX distribution.")

def run(command):
    subprocess.run(command, cwd=directory, check=True)

latex = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "paper.tex"]
run(latex)
if (directory / "references.bib").exists():
    run(["bibtex", "paper"])
run(latex)
run(latex)
log = (directory / "paper.log").read_text(errors="replace")
problems = [line for line in log.splitlines() if
    "undefined" in line.lower() or "Overfull" in line or "Rerun to get" in line]
if problems:
    raise SystemExit("Build needs review:\n" + "\n".join(problems))
print("Built", directory / "paper.pdf")
