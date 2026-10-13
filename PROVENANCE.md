# Provenance and verification

Prepared 25 September 2026. The repository owner selected the source papers, directed the
research, and requested this packet. The new arguments, code and prose were produced by AI
systems:

- **OpenAI Codex (GPT family; no more specific deployment identifier is asserted),
  20–21 September 2026:**
  - notes 02 (selector counterexample), 03 (temporal knower joint model), 04 (formula-language
    classification) and 05 (RL transformation counterexample);
  - the universality argument in §3 of the further-results document.
- **Anthropic Claude (Opus 5.5), 25 September 2026:**
  - notes 01 (quitters), 06 (founding-cohort species), 07 (minimal introspection bundle) and
    08 (internodon order robustness);
  - §§1, 2, 4 and 5 of the further-results document;
  - the assembly of this repository, which involved rewriting the working notes to be
    self-contained, with no external working references.

Claude re-checked the key claims of note 05 against the arXiv v5 text (Definition 2 and the
proof of Theorem 3) during assembly.

**Verification.**
- **The scripts are finite or exact-arithmetic controls.** Each script was re-run from this
  repository during assembly and reproduced its committed JSON output byte for byte.
- **At the initial September assembly, the infinite claims rested on the hand arguments
  in the notes.** The October addition below includes a Lean formalisation of the
  dissertation Questions 3-1-x.
- **No independent human mathematical review** has been recorded.

**Priority.** Targeted public searches, recorded in the individual notes, did not locate earlier
answers to these specific questions. A bounded negative search does not establish novelty.

**Sources.** Only our own text and code are included. The source papers are cited and linked,
not redistributed. Quotations from them are short and attributed.

**Status.** Nothing has been sent to Samuel Allen Alexander or his coauthors.

## 27 September 2026: audit and additions

At the owner's request, OpenAI Codex audited the repository. It:
- wrote the report, now summarised in `CORRECTIONS.md`;
- wrote the proofs in notes 10–13;
- wrote `audit-2026-09-27/controls.py`.

Anthropic Claude (Opus 5.5) then:
- verified each finding against the source papers and scripts, with a fresh re-computation of the
  internodon metrics (`08-internodon-order-robustness/comembership_check.py`);
- checked the four new proofs step by step;
- inserted the dated correction boxes;
- adapted notes 10–13 into self-contained form.

Only the path to the repository changed in the audit's controls script, and its output reproduces
the audit's byte for byte. No independent human review has been recorded, and nothing has been sent
to the source authors.

## 30 September 2026: dissertation Questions 3-1-x (notes 14–16)

OpenAI Codex (workspace actor `codex`), 28–29 September 2026, working at the owner's request:
- the construction and proof for Question 3-1-1;
- the construction and proof for Question 3-1-2 (transparent stratification, contextual collapse,
  induction over all external interpretations, rebuilt truth filters);
- the counterexample to Lemma 2.5.5.

Anthropic Claude (Opus 5.5), 30 September 2026:
- audited all three against the dissertation text, re-deriving every step;
- wrote out in full the two lemmas the Codex draft only sketched (note 15, Lemmas A and B);
- rewrote the three notes to be self-contained.

The audit found no error in any of the three. Note 15 is long, and it depends on stratification
lemmas that should be reviewed independently. Its status is **proposed**. Nothing here resolves
Question 3-1-3. No independent human review has been recorded, and nothing has been sent to the
author.

## 3 October 2026: dissertation Question 3-1-3 (note 17)

OpenAI Codex wrote the paper in note 17, at the owner's request. It expands the proposed hand
proof assembled over 30 September – 2 October 2026 in working notes that are not published
here. Its own [PROVENANCE.md](17-dissertation-question-3-1-3/archive/2026-10-03/PROVENANCE.md) lists those sources and
the checks recorded on them: a hand audit of the modal argument, conditional on its ordinal
input, and a follow-up verification of the uniform typed ordinal closure that condition required.

Anthropic Claude (Opus 5.5) moved the folder into this repository on 3 October 2026 and updated
its relative paths. The manuscript is unchanged, and no new mathematical audit was made at
placement. The status is **proposed**. No independent human review has been recorded, and
nothing has been sent to the author.

## 13 October 2026: dissertation naming and embedded Lean project

At the owner's request, OpenAI Codex renamed notes 14–17 and their index labels
to use dissertation terminology. Their mathematical text and PDFs are unchanged;
the phrase "mechanistic thesis" remains where it names Reinhardt's thesis or a
published paper. The earlier 3 October proof is retained.

The [embedded Lean project](alexander-dissertation-lean/README.md) is a tracked-file
copy of the standalone repository at `b06b50a`, including the revised 8 October
paper, its 31-page PDF and the detailed paper comparison. Its
[import record](alexander-dissertation-lean/IMPORT-PROVENANCE.json) preserves
the original repository identity and file hashes. All Lean source files are
unchanged; title and workflow labels use dissertation terminology.

The preceding proof checkpoint `02be37a` passed its focused
[GitHub workflow](https://github.com/avg-netizen/alexander-thesis-3-1-1-lean/actions/runs/38440882592).
Local validation of that development covered 321 project modules and 107 axiom
reports. This placement and naming change adds no new mathematical audit;
the embedded comparison and receipts state the formal result's scope.

## 13 October 2026: revised paper as the main note 17

At the owner's request, OpenAI Codex archived the earlier 3 October paper and
its build records under `17-dissertation-question-3-1-3/archive/2026-10-03/`.
The manuscript and PDF are unchanged. Relative references in the archived
documentation and source map were rebased for that location.

The [31-page revised paper](17-dissertation-question-3-1-3/archive/2026-10-08/REVISED-3-1-3-PROOF.pdf)
and its source and typesetting files are now directly in note 17, with links
at the top of the repository index and in the results table. They were copied
byte for byte from the embedded Lean project's existing paper bundle, which
remains intact. The [placement provenance](17-dissertation-question-3-1-3/PROVENANCE.md)
and source map record their identity and the archive location. No Lean proof
or mathematical text was edited in this reorganization.

## 13 October 2026: standalone exposition of the finite-guard proof

The owner clarified that the current paper must not assume familiarity with
the earlier proof. Codex read the complete manuscript and added a conventional
abstract, contextual introduction, explicit epistemic-arithmetic definitions,
and explanations of the auxiliary theory, stage roles and two inductions.
The mathematical auxiliary-strength consequences now stand on their own;
the historical comparison and handoff/module correspondence are in a companion note.

The current [33-page paper](17-dissertation-question-3-1-3/REVISED-3-1-3-PROOF.pdf)
is titled *Knowing machines with mutual truthfulness and mechanicalness*.
The main theorem, all 18 numbered lemma statements, all 104 displayed formulas
and all 888 mathematical expressions in Sections 1–17 are preserved.
The original 8 October edition and seven-file build bundle are archived
byte for byte. The embedded Lean project remains unchanged. The
[editorial review record](17-dissertation-question-3-1-3/standalone-editorial-review.json)
and [provenance](17-dissertation-question-3-1-3/PROVENANCE.md) state the precise
editorial and document-check scope. This is no new mathematical audit.
