---
title: "Knowing everyone's truthfulness and one's subordinates' codes"
subtitle: "An affirmative answer to Question 3-1-1 of S. A. Alexander, *The Theory of Several Knowing Machines* (2013)"
date: "30 September 2026"
---

**Status.**
- **Kind of proof:** a hand proof. Not machine-checked.
- **Checks:** it was written by one AI system and checked step by step by another; see the
  repository's provenance file. No independent human review.
- **Novelty:** the argument combines two techniques already in Alexander's work. What is new is
  their combination, and the answer to a question the dissertation lists as open.
- **Priority:** targeted searches found no earlier resolution. That is not a full priority check.

**Source.** S. A. Alexander, *The Theory of Several Knowing Machines*, doctoral dissertation,
Ohio State University, 2013 (OhioLINK ETD
[osu1366362999](https://etd.ohiolink.edu/acprod/odb_etd/ws/send_file/send?accession=osu1366362999&disposition=inline)).
The question is from §1.1, Definition 1.1.1 and Figure 1. Also cited: S. A. Alexander,
*Self-referential theories*, J. Symbolic Logic 85(4), 2020,
[arXiv:2008.11535](https://arxiv.org/abs/2008.11535).

**The question.** Let R be an r.e. well-founded relation on ℕ, where *j R i* is read "agent j is
subordinate to agent i". Question 3-1-1 asks whether it is consistent with self-doubting Epistemic
Arithmetic that every agent m satisfies three conditions:
- **(3-x-x)** m knows the truthfulness of everyone: $K_m(\mathrm{ucl}(K_n\varphi\to\varphi))$ for
  every n and every φ;
- **(x-1-x)** m knows codes for its subordinates: $\exists e\,K_m\forall x(K_n\varphi\leftrightarrow x\in W_e)$
  for every n R m and every φ with a single free variable x;
- **(x-x-1)** m knows the mechanicalness of its subordinates:
  $K_m\exists e\,\forall x(K_n\varphi\leftrightarrow x\in W_e)$ for n R m.

The dissertation answers 24 of the 27 questions in its matrix. It leaves the three Questions
3-1-x open and instead answers a variant, (3-1-2)′, in which m's knowledge of the truthfulness of
non-subordinates is restricted to formulas that do not expose $K_m$.

**Answer.** **Yes**, for every r.e. well-founded R. R need not be transitive.

# 1. Setting (the dissertation's §1.2)

The language $L_ω$ is the language of Peano arithmetic, extended by modal operators $K_i$
($i∈ℕ$).

**The base logic** (Definition 1.2.3).
- A structure interprets $Kφ[s]$ by an arbitrary truth value, subject to three conditions:
  - independence from variables that are not free;
  - invariance under alphabetic variants;
  - weak substitution of *variables*.
- Validity means truth in all structures.
- Semantic consequence ⊨ is effective (Theorem 1.2.6), and "consistent" means satisfiable.
- $φ^s$ substitutes numerals for free variables, including inside operators, so $(Kφ)^s≡K(φ^s)$
  (Lemma 1.2.12). Numeral instances of valid formulas need not be valid (Example 1.2.13); this is
  why *Assigned Validity* (every $φ^s$ with φ valid) is used below.

**Knowing machines.**
- A family $K_i\mapsto T_i$ of r.e. theories determines the **intended structure** $M_T$: standard
  arithmetic, with $M_T⊨K_iφ[s]$ iff $T_i⊨φ^s$.
- The family is a *family of knowing machines satisfying self-doubting EA* if $M_T$ satisfies the
  following:
  - for each i, the i-Validity, i-Reasoning, i-Introspection and i-Truth axioms;
  - $K_iψ$ for every instance ψ of the first three;
  - Peano arithmetic for $L_ω$ (induction for every formula);
  - $K_i$ applied to each PA axiom.

# 2. Construction

Fix effective codings. For each i and each parameter q, let $G_i(q)$ be the following set of
sentences.

1. The PA axioms of $L_ω$, and Assigned Validity.
2. i-Validity, i-Reasoning and i-Introspection (universal closures).
3. **Full reflection:** $\mathrm{ucl}(K_jφ→φ)$ for **every** j and every φ, including j = i and
   formulas exposing $K_i$.
4. **Codes:** for j R i and φ with $FV(φ)=\{x\}$,
   $$\forall x\,(K_jφ\leftrightarrow x∈W_{s(q,j,φ)}),\qquad W_{s(q,j,φ)}=\{m:⟨⌜φ⌝,j,m⟩∈W_q\},$$
   where s is an s-m-n function and the index is a numeral.

Let $A_i(q)=\{K_i^rσ : σ∈G_i(q),\ r≥0\}$, and let $T_i(q)$ be its set of consequences. Because R is
r.e., this family is uniformly r.e. in q and i. Take a total computable f with
$W_{f(q)}=\{⟨⌜φ⌝,j,m⟩:FV(φ)=\{x\},\ T_j(q)⊨φ(x|\bar m)\}$. The recursion theorem then gives q with
$W_q=W_{f(q)}$. Fix this q and write $T_i$ for $T_i(q)$. Then

$$m∈W_{s(q,j,φ)}\iff T_j⊨φ(x|\bar m).\tag{1}$$

**Lemma 1 (closure).** For every sentence θ, if $T_i⊨θ$ then $T_i⊨K_iθ$.

*Proof.* Finitely many $σ_l∈A_i$ make $σ_1→\dots→σ_r→θ$ valid.
- $K_i$ of that implication is an i-Validity instance.
- Each $K_iσ_l$ belongs to $A_i$.
- r applications of i-Reasoning give $K_iθ$.

All the formulas involved are sentences. □

# 3. Proof that the family works

**The provisional structure.** Define M on standard arithmetic, **by recursion on formula
complexity**:

$$M⊨K_iφ[s]\iff T_i⊨φ^s\ \text{and}\ M⊨φ[s].\tag{F}$$

This is the truth-filtered interpretation of the dissertation's dual proof (§2.3). The recursive
call is on a proper subformula, and the consequence relation on the left is fixed syntax, so (F)
presupposes no soundness.

M is a structure:
- **Free variables:** clear.
- **Alphabetic variants:** they are logically equivalent, and the truth clauses agree by
  induction.
- **Weak substitution:** $(φ(x|y))^s$ and $φ^{s(x|s(y))}$ are the same sentence.

Induction on formulas, using Lemma 1.2.12 at K, gives numeral-instance invariance:
$M⊨φ[s]\iff M⊨φ^s$.

**Step 1: every generator in items 1–3 is true in M, with no soundness assumption.**
- **PA:** holds because arithmetic is standard; modal induction follows from metatheoretic
  induction applied to each defined set.
- **Assigned Validity:** validity plus numeral invariance.
- **i-Validity:** $T_i⊨φ^s$ by Assigned Validity, and $M⊨φ[s]$ by validity.
- **i-Reasoning:** modus ponens holds on both sides of (F).
- **i-Introspection:** Lemma 1 gives $T_i⊨K_i(φ^s)≡(K_iφ)^s$, and the truth half of (F) is the
  hypothesis.
- **Reflection:** for every j it is exactly the truth half of (F).

**Step 2: M ⊨ $T_i$ for every i, by well-founded induction on R.** Assume $M⊨T_j$ for all j R i.
- **Codes.** For such j, the truth half of (F) is redundant. So for unary φ,
  $M⊨K_jφ[x↦m]\iff T_j⊨φ(x|\bar m)\iff m∈W_{s(q,j,φ)}$ by (1). The code generators are true.
- **The prefixes $K_i^rσ$.** They are true by induction on r: $σ∈T_i$, and σ is true.
- **Conclusion.** Every member of $A_i$ is true, hence so is every consequence: $M⊨T_i$.

The induction is sound because M is fixed before it starts. What is proved by induction is the
*statement* "$M⊨T_i$". It is not a fixed-point definition.

**Step 3: removing the filter.** Every $T_i$ is now true in M, so the truth half of (F) is
redundant everywhere and $M=M_T$. The requirements are then met:
- **Self-doubting EA:** Step 1 shows the axioms of knowledge hold. $T_i$ contains PA, the known
  versions (by closure), and truth.
- **(3-x-x)** is item 3.
- **(x-1-x)** is item 4, which also gives (x-x-1).

**Theorem.** For every r.e. well-founded R there is a uniformly r.e. family of knowing machines
satisfying self-doubting Epistemic Arithmetic and 3-1-1. In it, each machine also knows its own
truthfulness. ∎

# 4. Remarks

- **Why this is easy, and 3-1-2 is not.** Adding self-mechanicalness,
  $∃e∀x(K_iφ↔x∈W_e)$, as a generator of $T_i$ breaks Step 2. Under (F), its truth needs the
  intersection of an r.e. consequence set with a truth set to be r.e. Well-founded induction does
  not supply this, because the dependence is on $T_i$ itself. Question 3-1-2 is treated in note 15
  of this repository with ordinal stratification.
- **The comparison with *Self-referential theories*, Theorem 24.** That theorem uses the unfiltered
  structure $M_T$ with the same R-induction, and obtains truthfulness only toward strict
  subordinates. Filtering makes reflection toward *everyone* free of charge. The price is paid
  only by the code axioms, and there well-foundedness suffices.
- **A necessary asymmetry.** Suppose truthful A knows B's truthfulness and a code e for B on
  $δ(x)=x∉W_x$. Put $g=δ(e)$. Then A knows g and $¬K_Bg$, while B does not know g. Consequently:
  - A's arithmetic theorems strictly extend B's;
  - if B also knows A's truthfulness, then B cannot know that A knows g.

  In the family above this asymmetry is realised, not contradicted.
- **Self-loops are genuinely excluded.** With i R i, the induction hypothesis in Step 2 would be
  its own conclusion. By Reinhardt's argument, a machine that knows its own truthfulness and its
  own code is impossible.
