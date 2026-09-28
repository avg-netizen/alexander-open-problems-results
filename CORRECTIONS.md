# Corrections and additions, 27 September 2026

An external audit of this repository was carried out by OpenAI Codex at the owner's request. It
reviewed every note and its scripts, and it replicated the exact-arithmetic checks. Every finding
below was then checked independently by Anthropic Claude against:
- the source papers;
- the scripts;
- a fresh re-computation, for the internodon metrics.

The affected notes keep their original text. Each has a dated correction box at the top and inline
markers at the sentences concerned.

## Errors corrected

| Note | Severity | What was wrong | Correct statement |
|---|---|---|---|
| 08 internodons | **major** | "Species membership almost intact". The 4–14% all-pairs statistic is dominated by pairs that were never co-members. | Under within-generation reordering, 18–32% of originally co-clustered pairs are separated (up to 52–61% in single comparisons). Co-member Jaccard is 0.48–0.73. The two proved lemmas stand. |
| 08 internodons | minor | The "arbitrary order" sampler was called uniform. | It is uniform over *available vertices*, not over linear extensions (a→c plus b gives 1/4, 1/4, 1/2). |
| 08 internodons | minor | Singleton labels for organisms that are not SD and have no SD ancestor. | This is a code convention; Definition 9 puts such organisms in no internodon. Excluding them leaves the co-membership metrics unchanged in the audited draws. |
| 09 §1 P1a | **major** | A frozen seed was taken to imply independent visible and erased draws, and a strict gain was claimed. | Both steps fail: a shared coin flip gives no mismatch, and in the (1, 0) reward example the two optima are equal at 7/8. The correct private-query statement is note 12. |
| 06 founding cohort | **moderate** | "Any CA-free solution must exclude late founders". | Proposition 4 only rules out classes that contain *every* extension $S_α$. A fixed founder bound admits late founders (note 11). |
| 01 quitters | minor | "Neither hypothesis constrains the initial reward". | Bounded rewards gives r₁ ≤ 1. What fails for r ≤ 0 is the strict inequality r₁ < r + 1. The normalisation in §2 is pathwise. |
| 07, 09 §5.5 | minor | The stratified analogue of Lemma 19 was cited as Lemma 64. | It is Lemma 65. |
| 09 §2 | minor | Non-guessability of IAP was read as non-convergence on species classes. | The theorem concerns yes/no properties only. |
| 09 §3 | minor | "A 1 occurs somewhere" was called never certifiable. | It is positively certifiable at the first 1. It lacks a two-sided decision. |
| 09 §4 | clarification | The variadic-Apply card. | It must first fix a function sort, codes or an indexed operator family, and specify the semantics of the completeness theorem. |

The audit found no gap in the central arguments of notes 02, 03, 04, 05 and 07, or in the proved
parts of 01, 06 and 08, within their stated models.

## New results (notes 10–13)

| Note | Result | Resolves |
|---|---|---|
| 10 | Infinite founding-cohort and common-ancestor maximal clusters give the same ∼-classes (via Alexander's Objective Species Theorem). Global IAP is Π⁰₃-complete on connected rooted binary trees. | Conjecture S1 (06, 09 §5.1); Conjecture 2b (09 §2) |
| 11 | With a fixed founder budget N, the class is upward generic and covers every organism. For N ≥ 2 it admits late founders and maximal clusters with no common ancestor. | Corrects 06; a second CA-free answer |
| 12 | An exact value formula for a private counterfactual annotation. Counterexamples to unconditional P1a. P1b proved for finite contextual bandits with sample-average tabular updates and unique maximisers. | Corrects and partly proves 09 §1 |
| 13 | Under the 2021 expected-value normalisation, for every r there is a symmetric universal machine giving a Question 26 counterexample. Under the pathwise normalisation, the implication holds for r ≥ 0. | Conjecture 5.4 (09), in "∃U" form; the fixed-U form is open |

## Checks

- `audit-2026-09-27/controls.py` → `controls.json`. It covers:
  - the IAP-reduction invariants;
  - the sampler distribution;
  - the private-information values;
  - the signed-quitting margins and tape checks (8,748);
  - the internodon contingency counts.

  Re-run from this repository, it reproduces the audit's output byte for byte.
- `08-internodon-order-robustness/comembership_check.py` → `comembership-check.json`: the
  independent re-computation of lost co-membership.
- The infinite claims rest on the hand proofs in the notes. No proof-assistant check was run.
