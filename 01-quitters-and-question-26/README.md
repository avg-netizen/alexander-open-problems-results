# Quitting thresholds and reward normalization

[Full paper (PDF)](quitters.pdf) ·
[Canonical Markdown](quitters.md) ·
[Generated TeX](quitters.tex)

The paper combines entries 01 and 13. It gives a full proof of the
ultrafilter threshold boundary, answers Question 26 under nonnegative
pathwise reward summability, and constructs signed expected-value
counterexamples with a chosen symmetric universal prior.
The quantifier is for every threshold there exists a suitable machine;
the arbitrary fixed-machine question is not settled.

## Rebuild

From the repository root:

~~~sh
python3 build_documents.py 01-quitters-and-question-26
~~~

Requirements are Python 3, Pandoc 3, Tectonic and Poppler. The PDF
uses Computer Modern and cached TeX resources by default; add
--allow-downloads if resources are missing. Its included vector
figure suffices for the build. Regenerating it with make_figures.py
requires Matplotlib and draws the explicit K=3 construction.

The original [exact rational controls](quitters_check.py) and
[saved output](quitters_check.json) are unchanged. Signed margins and
finite tape checks are in the existing
[audit program](../audit-2026-09-27/controls.py) and
[record](../audit-2026-09-27/controls.json).
Rebuilding the paper does not execute them.

See [SOURCES.md](SOURCES.md), [the build report](pdf-build-report.json)
and [the revision record](../REVISIONS.md). The
[September edition](archive/2026-09-27/README.md) is historical.
The arguments remain hand proofs without independent human review.
