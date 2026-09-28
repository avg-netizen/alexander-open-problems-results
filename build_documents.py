#!/usr/bin/env python3
"""Rebuild every PDF in this repository from its Markdown source.

Requires pandoc (>= 3) and tectonic, plus the DejaVu fonts (DejaVu Serif, DejaVu Sans Mono,
DejaVu Math TeX Gyre), which cover the Unicode mathematics used in the notes;
`preamble.tex` maps the two glyphs DejaVu Serif lacks (U+220E, U+22EF) to the math font.
Usage:  python3 build_documents.py [--allow-downloads] [folder ...]
By default tectonic runs with --only-cached; pass --allow-downloads on a first run so it can
fetch the LaTeX packages it needs.
"""
import argparse
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DOCUMENTS = {
    "01-quitters-and-question-26": "quitters",
    "02-selector-counterexample": "selector-counterexample",
    "03-temporal-knower-joint-model": "temporal-knower-joint-model",
    "04-formula-language-classification": "formula-classification",
    "05-rl-transformation-counterexample": "rl-transformation-counterexample",
    "06-founding-cohort-species": "founding-cohort-species",
    "07-minimal-introspection-bundle": "minimal-introspection-bundle",
    "08-internodon-order-robustness": "internodon-order-robustness",
    "09-further-results": "further-results",
    "10-species-equivalence-and-iap-completeness": "species-equivalence-and-iap-completeness",
    "11-bounded-founders": "bounded-founders",
    "12-pseudovisibility-private-information": "pseudovisibility-private-information",
    "13-signed-quitting": "signed-quitting",
}
PANDOC_VARS = [
    "mainfont=DejaVu Serif", "monofont=DejaVu Sans Mono", "mathfont=DejaVu Math TeX Gyre",
    "fontsize=10pt", "geometry:margin=2.4cm", "colorlinks=true", "linkcolor=blue",
    "urlcolor=blue",
]

parser = argparse.ArgumentParser()
parser.add_argument("--allow-downloads", action="store_true")
parser.add_argument("folders", nargs="*", default=list(DOCUMENTS))
args = parser.parse_args()

for folder in args.folders:
    stem = DOCUMENTS[folder]
    cwd = ROOT / folder
    cmd = ["pandoc", "-f", "markdown+lists_without_preceding_blankline", f"{stem}.md", "-s", "-H", str(ROOT / "preamble.tex"), "-o", f"{stem}.tex"]
    for v in PANDOC_VARS:
        cmd += ["-V", v]
    subprocess.run(cmd, cwd=cwd, check=True)
    tect = ["tectonic", "--keep-logs"] + ([] if args.allow_downloads else ["--only-cached"])
    subprocess.run(tect + [f"{stem}.tex"], cwd=cwd, check=True)
    print("built", cwd / f"{stem}.pdf")
