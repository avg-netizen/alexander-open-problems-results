# Results on open problems from the papers of Samuel Allen Alexander

This repository is a research packet for discussion. It is not a journal submission, and it
makes no claim to established priority. Each folder holds one self-contained note: Markdown
source, a PDF, and any scripts with their recorded output.

The notes answer, correct or sharpen questions posed in Alexander's papers on:
- universal intelligence;
- self-referential logic;
- epistemic logic;
- formula languages;
- reinforcement-learning frameworks;
- mathematical biology.

A companion packet on *Biologically unavoidable sequences* is published separately:
[biological-unavoidability-results](https://github.com/avg-netizen/biological-unavoidability-results).
Nothing here duplicates it.

## Standalone results

| # | Result | Source question | Status |
|---|---|---|---|
| 01 | [Quitters](01-quitters-and-question-26/quitters.pdf): Proposition 20 is false as printed for r ≤ 0 (true for r > 0). Question 26 under Legg–Hutter normalisation: yes iff r ≥ 0. | *Intelligence via Ultrafilters* (2019), Prop. 20, Q. 26 | hand proof + exact check |
| 02 | [Selector counterexample](02-selector-counterexample/selector-counterexample.pdf): an explicit universal machine for which observation-based selection reverses universal-intelligence rankings. | *Intelligence via Ultrafilters*, Q. 23–25 | hand proof + exact check |
| 03 | [Temporal knower joint model](03-temporal-knower-joint-model/temporal-knower-joint-model.pdf): a factive model of the surprise-examination theory extended by self-referential sentences L_i, with later knowledge of their falsehood. | Aldini–Alexander–Graziani (2023), concluding conjecture | proposed resolution, hand proof + finite controls |
| 04 | [Formula-language classification](04-formula-language-classification/formula-classification.pdf): the 2006 language describes exactly the partial functions with arithmetical graphs. | *Formulas for Computable and Noncomputable Functions* (2006), after Cor. 9 | hand proof |
| 05 | [RL transformation counterexample](05-rl-transformation-counterexample/rl-transformation-counterexample.pdf): maps satisfying the printed Definition 2 that contradict Theorem 3. | *Representation and Invariance in RL*, arXiv v5 (2026) | explicit counterexample |
| 06 | [Founding-cohort species](06-founding-cohort-species/founding-cohort-species.pdf): a CA-free axiom set that is upward generic and covers every organism; maximal species may have several founders. | *Specieslike Clusters* (2026), after Thm. 13 | hand proof |
| 07 | [Minimal introspection bundle](07-minimal-introspection-bundle/minimal-introspection-bundle.pdf): i-Validity is redundant in Lemma 19; {Assigned Validity, i-Deduction} is the unique minimal bundle. | *Self-referential Theories* (2020), after Cor. 23 | hand proof + countermodels |
| 08 | [Internodon order robustness](08-internodon-order-robustness/internodon-order-robustness.pdf): the undirforest is a merge tree; one adjacent swap changes at most one clade; measured robustness of internodon partitions. | *Alternative Construction of Internodons* (2015), concluding conjecture | two lemmas + measurements |

## Further results

[further-results.pdf](09-further-results/further-results.pdf) collects:
- **Pseudo-visibility.** A formalisation of the "better-performance" conjecture, with a proved
  stochastic-policy case and an experiment. The experiment shows the deterministic tabular gain
  is only in rates.
- **Species identity.** A theorem that it is not learnable in the limit: no observer of births
  converges on whether IAP holds, or on whether a split is permanent.
- **Universality.** The same limit-learning impossibility for universality of the companion
  packet's avoiding populations.
- **Problem statements** for pattern algorithms (ε, φ) and variadic Apply.
- **Seven conjectures,** each with a proof route or test.

## Reproducing

The scripts need Python 3; `08` and `09` also need numpy. Run each script from its own folder:
it rewrites its JSON output, which should match the committed file byte for byte. The longest
runs (`08/order_robustness.py`, `09/pseudovisibility/selfrefl_exp.py`) take a few minutes.

To rebuild the PDFs: `python3 build_documents.py --allow-downloads`. This needs pandoc ≥ 3,
tectonic and the DejaVu fonts. `SHA256SUMS` lists checksums of the committed files.

## Provenance

See [PROVENANCE.md](PROVENANCE.md). In brief:
- the arguments, code and prose were produced by AI systems under the direction of the repository
  owner;
- no independent human mathematical review has been recorded;
- nothing has been sent to the authors of the source papers.
