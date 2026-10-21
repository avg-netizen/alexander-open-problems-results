# Specieslike clusters with several founders

[Full paper (PDF)](founding-cohort-species.pdf) ·
[Canonical Markdown](founding-cohort-species.md) ·
[Generated TeX](founding-cohort-species.tex)

This paper combines the results formerly presented separately in entries
06, 10 and 11. One finite-founder chain argument proves coverage for
founding cohorts and for any fixed finite founder bound. The paper then
compares the infinite generator-equivalence classes and proves a Borel
complexity theorem for global IAP.

The coverage results answer Alexander's request following Theorem 13
of *Specieslike clusters based on identical ancestor points*. The
equivalence and complexity questions originated in this repository.
They are distinguished in the paper; not every theorem answers a
previously published open question.

See [SOURCES.md](SOURCES.md) for the primary-source locations and
dependencies, [the build report](pdf-build-report.json) for document
checks, and [the repository revision record](../REVISIONS.md) for the
relationship to earlier editions. These are hand proofs, without an
independent human review or a formal certificate.

## Rebuild

From the repository root:

~~~sh
python3 build_documents.py 06-founding-cohort-species
~~~

The build requires Python 3, Pandoc 3, Tectonic and Poppler's
pdftotext, pdffonts and pdfinfo. It uses Computer Modern. The default
build uses cached TeX resources; add --allow-downloads on the first
run if needed. The included vector figure is sufficient for rebuilding
the paper. To regenerate it, run make_figures.py from any directory;
this optional step requires Matplotlib.

The [September edition](archive/2026-09-27/README.md) is an archive.
The current paper presents the operative statements directly, without
asking the reader to reconstruct them from correction boxes.
