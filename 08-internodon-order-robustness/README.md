# Birth-order sensitivity of undirforests and internodons

[Full paper (PDF)](internodon-order-robustness.pdf) ·
[Canonical Markdown](internodon-order-robustness.md) ·
[Generated TeX](internodon-order-robustness.tex)

The paper explains the component-sweep construction, proves the exact
effect of an adjacent birth-order swap, and derives a clade-distance
bound between topological orders. It separates these results from
height stability and from measured internodon co-membership.

In the dedicated saved comparison sample, the mean loss of reference
co-member pairs ranges from 18.06% to 30.83%; the largest individual
loss is 60.67%. These rates use a different denominator from all-pairs
disagreement. They are finite model measurements, not a resolution of
the source's general biological robustness question.

See [SOURCES.md](SOURCES.md) for definitions, imported theorem hypotheses
and experiment protocols, [the build report](pdf-build-report.json)
for document checks, and [the revision record](../REVISIONS.md) for
historical changes.

## Rebuild

From the repository root:

~~~sh
python3 build_documents.py 08-internodon-order-robustness
~~~

Requirements are Python 3, Pandoc 3, Tectonic and Poppler. The current
paper uses Computer Modern. Add --allow-downloads if TeX resources
are not cached. The included vector figures are sufficient for the
PDF build. Regenerating them with make_figures.py requires Matplotlib
and reads the saved co-membership record; it does not run simulations.

## Computational material

The scripts and their existing JSON records are retained unchanged.
Rebuilding the PDF does not execute these experiments.

| Program | Record | Scope |
|---|---|---|
| [undirforest.py](undirforest.py) | — | Direct definition and component sweep |
| [swap_locality.py](swap_locality.py) | [swap-locality.json](swap-locality.json) | Adjacent-swap finite controls |
| [comembership_check.py](comembership_check.py) | [comembership-check.json](comembership-check.json) | Reference co-member loss, all-pairs disagreement and Jaccard |
| [order_robustness.py](order_robustness.py) | [order-robustness.json](order-robustness.json) | Separate parent-pointer, clade and all-pairs sample |
| [order_robustness.py](order_robustness.py), buffered argument | [order-robustness-buffered.json](order-robustness-buffered.json) | Future-buffer experiment |
| [order_robustness_any.py](order_robustness_any.py) | [order-robustness-any.json](order-robustness-any.json) | Kahn-order sample |

The [earlier paper and PDF](archive/2026-09-27/README.md) are archived.
The operative manuscript contains the current mathematics and
measurements directly. The arguments remain hand proofs; finite
checks do not certify the universal theorems.
