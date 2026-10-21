# Sources, definitions and computational scope

## Primary construction

S. A. Alexander, A. de Bruin and D. J. Kornet,
*An alternative construction of internodons: the emergence of a
multi-level tree of life*, Bulletin of Mathematical Biology (2015),
[DOI 10.1007/s11538-014-0048-2](https://doi.org/10.1007/s11538-014-0048-2).

- Definition 4 defines undirancestry through a path avoiding elders.
- Definition 5 and Corollary 6 identify the immediate or youngest
  undirancestor as the derived parent.
- Definition 7 defines SD using a strict genealogical descendant
  with at least two parents, and defines a non-SD organism's test.
- Definitions 8–9 define SD segments and internodons. The branching
  vertex ends its own segment; its children start new segments.
  A non-SD organism with no SD ancestor has no internodon.
- Section 8 asks about dependence on topological birth order.

The paper's Theorems 1–2 and Corollary 3 concern finite graphs.
The distinction from the infinite-future biological setting is
explicit. Singleton labels for uncovered organisms are a
computational reporting convention, not an added source definition.

## Imported height-stability theorem

Dmitriy Morozov, Kenes Beketayev and Gunther H. Weber,
*Interleaving Distance between Merge Trees*, TopoInVis 2013
[author manuscript](https://www.mrzv.org/publications/interleaving-distance-merge-trees/manuscript/),
Theorem 2, pp. 6–7.

The theorem bounds merge-tree interleaving distance by the sup norm
of two scalar functions on the same domain. Section 4 applies it
to piecewise-linear negative birth ranks on the same connected
finite graph, retaining the standard infinite root ray. The
disconnected case is treated componentwise. This is a height
statement and provides no fixed-organism membership bound.

## Retained records

All counts below describe the existing saved records. The editorial
rewrite did not replace the scripts, seeds or JSON data.

| Record | Protocol |
|---|---|
| comembership-check.json | Seed 7; 14 generations, split at 6; four genealogies and six alternative within-generation rankings per configuration; four configurations |
| order-robustness.json | Seed 15; same generation/split parameters; six genealogies and twelve alternatives per configuration; nine configurations |
| order-robustness-buffered.json | Seed 16; evaluate ten generations, split at 4; buffers 0, 4, 8, 12; five genealogies and eight alternatives per configuration |
| order-robustness-any.json | Seed 21; five genealogies and ten Kahn orders per configuration; four configurations |
| swap-locality.json | Seed 44; 250 small random-graph trials; 4,302 valid swaps, 1,637 with a shared younger component |

The two main tables use different genealogical draws. Each table
entry is a mean of comparison-level rates, not a pooled-pair estimate
or a confidence interval. The buffered record does not contain
reference co-member loss. Choosing uniformly among currently
available vertices in Kahn's algorithm is not uniform sampling of
linear extensions.

The current co-membership table and plot are derived from
comembership-check.json: mean losses 22.41%, 18.06%, 22.16%, 30.83%;
maximum individual loss 60.67%. The broader numerical ranges in the
historical audit describe its own retained calculations and are not
substituted for these four rows.

The paper defines all metric denominators and distinguishes
finite-window labels from the infinite-future construction. Its
proofs do not depend on the simulations. No external working notes
are required.
