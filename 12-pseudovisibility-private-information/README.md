# Information and learning in pseudo-visibility environments

[Full paper (PDF)](pseudovisibility-private-information.pdf) ·
[Canonical Markdown](pseudovisibility-private-information.md) ·
[Generated TeX](pseudovisibility-private-information.tex)

This paper brings together the operative results formerly split between
09 Section 1 and 12. It explains deterministic representation, the exact
value of private annotations, shared-randomness coupling, and a restricted
tabular convergence theorem. A worked example separates the limiting
greedy policy from the joint policy-dependent optimum.

The finite-horizon comparisons and figure use the unchanged
[experiment record](../09-further-results/pseudovisibility/selfrefl_exp.json)
and [program](../09-further-results/pseudovisibility/selfrefl_exp.py).
The program's stochastic branch has a separate query stream and reuses
the annotation as the environment's query answer. The paper states this
protocol explicitly; the older program comments are not an implication
that a frozen random seed alone guarantees independence.

## Rebuild

From the repository root:

~~~sh
python3 build_documents.py 12-pseudovisibility-private-information
~~~

Python 3, Pandoc 3, Tectonic and Poppler are required. The default build
uses cached TeX resources; add --allow-downloads if needed on a first run.
The PDF uses Computer Modern. The included figure suffices for the build.
Regenerating it with make_figures.py requires Matplotlib and reads the
saved record; it does not run training.

See [SOURCES.md](SOURCES.md), [the build report](pdf-build-report.json),
and [the revision record](../REVISIONS.md).
The [September edition](archive/2026-09-27/README.md) is historical.
These remain hand proofs without independent human review.
