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
- **The infinite claims rest on the hand arguments in the notes.** No proof-assistant
  formalisation exists for any result here.
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
