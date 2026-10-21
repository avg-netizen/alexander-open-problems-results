# Results on open problems from the papers of Samuel Allen Alexander

This repository is a research packet for discussion. It is not a journal submission, and it
makes no claim to established priority. Each numbered folder is a research entry with
paper sources, a PDF or a pointer to a consolidated paper, and any scripts with their recorded output.

**Explanatory editions, 21 October 2026:**
[Specieslike clusters with several founders](06-founding-cohort-species/founding-cohort-species.pdf)
combines entries 06, 10 and 11 into one paper.
[Birth-order sensitivity of undirforests and internodons](08-internodon-order-robustness/internodon-order-robustness.pdf)
presents the structural results and the measurements with explicit metric denominators.
The current papers state corrected results directly; earlier editions and
[revision history](REVISIONS.md) are kept separately.

**Current 3-1-3 proof:** [33-page standalone PDF](17-dissertation-question-3-1-3/REVISED-3-1-3-PROOF.pdf)
· [manuscript](17-dissertation-question-3-1-3/REVISED-3-1-3-PROOF.md)
· [Lean proofs](alexander-dissertation-lean/README.md)
· [passing public CI](https://github.com/avg-netizen/alexander-open-problems-results/actions/runs/38453360717).
Earlier editions are retained in the [3 October archive](17-dissertation-question-3-1-3/archive/2026-10-03/README.md)
and the [8 October archive](17-dissertation-question-3-1-3/archive/2026-10-08/README.md).

**New, 20 October 2026:** [Open Problem 3.2.1 — successor chains without ordinal knowledge](18-dissertation-problem-3-2-1/README.md).
The [full paper](18-dissertation-problem-3-2-1/successor-knowers-3-2-1.pdf)
gives a negative answer by reduction to Pakhomov–Walsh, with
[supplemental proved consequences](18-dissertation-problem-3-2-1/supplemental/README.md).
This is a self-contained hand-proof entry, separate from the 3-1-x Lean development.

The notes answer, correct or sharpen questions posed in Alexander's papers on:
- universal intelligence;
- self-referential logic;
- epistemic logic;
- formula languages;
- reinforcement-learning frameworks;
- mathematical biology.

<details>
<summary>Historical research updates (27 September–3 October 2026)</summary>

> **27 September 2026:** an external audit found three substantive errors, in notes 06, 08 and
> 09, and several minor ones. They are corrected in place with dated boxes; see
> [CORRECTIONS.md](CORRECTIONS.md). The audit also contributed four new results, notes 10–13.

> **30 September 2026:** notes 14–16 concern the three questions the dissertation left open,
> Questions 3-1-x. 3-1-1 is answered. 3-1-2 has a proposed answer that is long and needs
> independent review. Note 16 shows a gap in the printed proof of the dissertation's partial
> result. **Question 3-1-3 remains open.**

> **3 October 2026:** note 17 is a standalone paper giving a **proposed** affirmative hand proof
> of Question 3-1-3, for every r.e. well-founded hierarchy. Questions 3-1-1 and 3-1-2 follow as
> corollaries. It has had recorded AI hand checks but no independent human review, and its Lean
> formalisation was incomplete at that checkpoint. This earlier paper is now archived.

</details>

> **13 October 2026:** the [Lean formalisation](alexander-dissertation-lean/README.md)
> is included here, with unconditional proofs of the independent comparator targets
> for Questions 3-1-1, 3-1-2 and 3-1-3. The [revised finite-guard proof PDF](17-dissertation-question-3-1-3/REVISED-3-1-3-PROOF.pdf)
> and [paper-to-Lean comparison](alexander-dissertation-lean/paper/LEAN-COMPARISON-2026-10-13.md)
> accompany it. The comparison records the construction differences and formal scope.
> Note 17 now presents this revision directly; the earlier paper and its build
> records are preserved in its dated archive. The dated entries above retain their historical status.

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
| 06 | [Specieslike clusters with several founders](06-founding-cohort-species/founding-cohort-species.pdf): founding cohorts and fixed finite founder bounds give CA-free coverage; their infinite generator-equivalence classes agree with the common-ancestor family. Includes the IAP complexity result from 10. | *Specieslike Clusters* (2026), after Thm. 13; derived questions from this repository | unified explanatory hand-proof paper (06 + 10 + 11) |
| 07 | [Minimal introspection bundle](07-minimal-introspection-bundle/minimal-introspection-bundle.pdf): i-Validity is redundant in Lemma 19; {Assigned Validity, i-Deduction} is the unique minimal bundle. | *Self-referential Theories* (2020), after Cor. 23 | hand proof + countermodels |
| 08 | [Birth-order sensitivity of undirforests and internodons](08-internodon-order-robustness/internodon-order-robustness.pdf): exact adjacent-swap and clade-distance theorems; separate height stability and co-membership measurements. The dedicated saved sample loses 18–31% of reference co-member pairs on average. | *Alternative Construction of Internodons* (2015), concluding question | explanatory hand proofs + finite measurements; general robustness remains open |
| 10 | [Species equivalence and IAP complexity](10-species-equivalence-and-iap-completeness/README.md): global IAP is Borel Π⁰₃-complete on connected rooted binary trees; infinite-class comparison. | Conjectures S1 and 2b of this repository | incorporated into 06, Sections 5–7 and Appendix A |
| 11 | [Bounded founders](11-bounded-founders/README.md): a fixed founder budget gives coverage and admits late founders. | *Specieslike Clusters*, after Thm. 13 | incorporated into 06, Sections 2–5 |
| 12 | [Pseudo-visibility, private information](12-pseudovisibility-private-information/pseudovisibility-private-information.pdf): exact value formula; counterexamples to unconditional P1a; restricted P1b convergence theorem. | *Pseudo-visibility* (2022), better-performance conjecture | hand proof (audit) |
| 13 | [Signed quitting](13-signed-quitting/signed-quitting.pdf): for every r, a symmetric universal machine with a Question 26 counterexample under expected-value normalisation. | *Intelligence via Ultrafilters*, Q. 26; *Reward-Punishment Symmetric Universal Intelligence* | hand proof + finite checks (audit) |
| 14 | [Dissertation Question 3-1-1](14-dissertation-question-3-1-1/several-knowing-machines-3-1-1.pdf): machines that know everyone's truthfulness and particular codes of their subordinates exist for every r.e. well-founded hierarchy. | *The Theory of Several Knowing Machines* (dissertation, 2013), Def. 1.1.1, Fig. 1 | hand proof (checked by a second AI system) |
| 15 | [Dissertation Question 3-1-2](15-dissertation-question-3-1-2/several-knowing-machines-3-1-2.pdf): add known own mechanicalness, still with unrestricted mutual truthfulness. Proposed: transparent stratification, contextual collapse, induction over all external interpretations. | same, Def. 1.1.1; strengthens Thm. 2.5.11 | **proposed** hand proof; long, needs independent review |
| 16 | [Lemma 2.5.5 counterexample](16-dissertation-lemma-2-5-5/dissertation-lemma-2-5-5.pdf): the dissertation's preservation lemma is false as printed, which leaves a gap in the proof of Thm. 2.5.11 (the theorem itself is not refuted). | same, Lemma 2.5.5, Thm. 2.5.11 | explicit countermodel |
| 17 | [Dissertation Question 3-1-3 — standalone finite-guard proof](17-dissertation-question-3-1-3/REVISED-3-1-3-PROOF.pdf): knowing machines that know everyone's truthfulness, particular codes of their subordinates, and everyone's mechanicalness exist for every r.e. well-founded hierarchy and unrestricted modal formulas. Current 33-page paper with abstract and complete introduction; [earlier editions archived](17-dissertation-question-3-1-3/README.md#earlier-editions-and-construction-history). | same, Def. 1.1.1, Question 3-1-3 | standalone prose proof; completed comparator targets pass public Lean CI; scope recorded in the comparison |
| 18 | [Dissertation Open Problem 3.2.1](18-dissertation-problem-3-2-1/successor-knowers-3-2-1.pdf): no infinite successor chain with full particular-code knowledge and known successor truthfulness in the standard canonical semantics, even without ordinal knowledge. [Supplement](18-dissertation-problem-3-2-1/supplemental/README.md) includes uniform enumeration, computable-path and arithmetic separation consequences. | same, §3.2, Open Problem 3.2.1, printed p. 89 | full hand proof using Pakhomov–Walsh; no independent human review or formal certificate |

## Dissertation formalisation and revised proof

[![Dissertation proof CI](https://github.com/avg-netizen/alexander-open-problems-results/actions/workflows/compile-dissertation-lean.yml/badge.svg?branch=main)](https://github.com/avg-netizen/alexander-open-problems-results/actions/workflows/compile-dissertation-lean.yml)

The public [proof-compilation workflow](.github/workflows/compile-dissertation-lean.yml)
builds the completed proof dependencies and checks all three unconditional
comparator targets, the effective ordinal core and the added paper conclusions.
Every gate audits its axioms against `propext`, `Classical.choice` and `Quot.sound`.
The run publishes logs and exact source hashes. The retained unfinished Wilken
aggregate is outside this build.

[alexander-dissertation-lean/](alexander-dissertation-lean/README.md) contains
the full tracked Lean project, including the earlier Wilken development and the
completed Carlson route. Its [import record](alexander-dissertation-lean/IMPORT-PROVENANCE.json)
pins source commit `b06b50a` and records every copied file's hash. All 1,294 Lean
source files are unchanged; the copy uses dissertation terminology in its title
and workflow labels. Existing Lean identifiers and historical repository URLs
retain their original spelling.

The [33-page standalone proof](17-dissertation-question-3-1-3/REVISED-3-1-3-PROOF.pdf)
is available directly in note 17 with its [Markdown source](17-dissertation-question-3-1-3/REVISED-3-1-3-PROOF.md)
and [detailed formalisation comparison](alexander-dissertation-lean/paper/LEAN-COMPARISON-2026-10-13.md).
Reproduction commands are in the embedded project's README. Build dependencies
and caches are fetched by Lake rather than included in this repository.
The comparison audits the [archived 8 October parent](17-dissertation-question-3-1-3/archive/2026-10-08/README.md).
The current paper supplies a standalone abstract, introduction and background
definitions while preserving the theorem and the main proof's mathematical expressions.

## Further results

[further-results.pdf](09-further-results/further-results.pdf) collects:
- **Pseudo-visibility.** A formalisation of the "better-performance" conjecture, with an
  experiment. The stochastic-policy case (P1a) was **wrong as stated**; see note 12.
- **Species identity.** A theorem that it is not learnable in the limit: no observer of births
  converges on whether IAP holds, or on whether a split is permanent.
- **Universality.** The same limit-learning impossibility for universality of the companion
  packet's avoiding populations.
- **Problem statements** for pattern algorithms (ε, φ) and variadic Apply.
- **Seven conjectures,** each with a proof route or test. Two are now resolved (notes 10 and 13).

## Reproducing

The scripts need Python 3; `08` and `09` also need numpy. Run each script from its own folder:
it rewrites its JSON output, which should match the committed file byte for byte. The longest
runs (`08/order_robustness.py`, `09/pseudovisibility/selfrefl_exp.py`) take a few minutes.

The audit checks are in `audit-2026-09-27/controls.py`.

To rebuild the PDFs: `python3 build_documents.py --allow-downloads`. This needs pandoc ≥ 3,
tectonic. The current editions of 06, 08, 10 and 11 use Computer Modern
through [build_explanatory.py](build_explanatory.py), with Poppler for document checks;
the other notes built by the root command retain DejaVu.
Note 17 has its own Markdown-to-PDF build script;
see [its README](17-dissertation-question-3-1-3/README.md). The archived 3 October
LaTeX paper retains its original build script in its archive.
Note 18 has a separate [offline build](18-dissertation-problem-3-2-1/README.md#rebuild)
for its main paper and supplement; the Markdown files are their canonical sources.
`SHA256SUMS` lists checksums of the committed files.

## Provenance

See [PROVENANCE.md](PROVENANCE.md). In brief:
- the arguments, code and prose were produced by AI systems under the direction of the repository
  owner;
- no independent human mathematical review has been recorded;
- nothing has been sent to the authors of the source papers.
