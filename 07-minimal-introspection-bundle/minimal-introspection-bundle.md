---
title: "Minimal building blocks for introspection in self-referential theories"
subtitle: "An answer to the minimality question after Corollary 23 of S. A. Alexander, *Self-referential theories* (2020)"
date: "25 September 2026"
---

**Status.** Hand proofs with explicit countermodels. Not machine-checked; no independent review.
The literature was not checked for priority.

**Source.** S. A. Alexander, *Self-referential theories*, Journal of Symbolic Logic 85(4), 2020.
[arXiv:2008.11535](https://arxiv.org/abs/2008.11535),
[doi:10.1017/jsl.2020.54](https://doi.org/10.1017/jsl.2020.54).

**The question.** After Corollary 23: "It would be interesting to investigate questions about
whether the above building-blocks are minimal. For example, in Lemma 19, is it really necessary to
bundle j-Introspection with all three other schemas? For now, we will leave those questions
open."

**Answer.**
- **No: i-Validity is redundant.** [AV]ᵢ ∪ [i-Deduction]ᵢ ∪ [i-Introspection]ⱼ is already
  closed-r.e.-generic.
- **The other two are both needed.** Dropping Assigned Validity (AV) or i-Deduction destroys
  genericity. So {AV, i-Deduction} in theory i is the **unique minimal** bundle that makes
  i-Introspection in theory j generic, among subsets of Lemma 19's three schemas.

# Setting (the paper's §§2–3)

- **The base logic.** The operator Tᵢ is interpreted in a structure by an arbitrary truth value
  M ⊨ Tᵢφ[s], subject only to Definition 2's three conditions: independence of non-free variables,
  alphabetic variants, and substitution of *variables*.
- **Validity** means truth in all such structures.
- **The substitution instance** φˢ replaces free variables by numerals, including inside operators,
  so (Tᵢφ)ˢ ≡ Tᵢ(φˢ).
- **The intended structure** $M_U$ of a family U sets $M_U$ ⊨ Tᵢφ[s] ⟺ Uᵢ ⊨ φˢ.
- **Closed-r.e.-generic** means: $M_U$ ⊨ T for every closed (each Uᵢ contains Tᵢσ for σ ∈ Uᵢ), r.e.
  family U ⊇ T.
- **The schemas:**
  - AV = {φˢ : φ valid};
  - i-Validity (iV) = ucl(Tᵢφ) for φ valid;
  - i-Deduction (iD) = ucl(Tᵢ(φ→ψ) → Tᵢφ → Tᵢψ);
  - i-Introspection (iI) = ucl(Tᵢφ → TᵢTᵢφ).

**The fact that makes AV non-trivial.** Validity is *not* closed under substituting numerals
inside operators, because Definition 2 links Tₖφ(x|y) with Tₖφ[s(x|s(y))] only for variables y.
- *Example.* χ(x) ≡ ∀y (y = x → (Tₖθ(y) ↔ Tₖθ(x))) is valid, by condition 3.
- But χ(n) ≡ ∀y (y = n → (Tₖθ(y) ↔ Tₖθ(n))) is not valid: nothing ties the atom Tₖθ(n), with
  its numeral, to the value of Tₖθ(y) at y = n.

# What introspection needs

For an assignment s, $M_U$ ⊨ (Tᵢφ → TᵢTᵢφ)[s] ⟺ (Uᵢ ⊨ φˢ ⇒ Uᵢ ⊨ Tᵢ(φˢ)). Every sentence is some
φˢ. So:

> **$M_U$ ⊨ i-Introspection ⟺ Uᵢ ⊨ ψ implies Uᵢ ⊨ Tᵢψ, for every sentence ψ.**

# Theorem 1. [AV]ᵢ ∪ [iD]ᵢ ∪ [iI]ⱼ is closed-r.e.-generic

It is r.e. by the paper's Theorem 3. Let U ⊇ the family be closed and r.e.
- **The AV and iD parts** are true in $M_U$, by the paper's Lemmas 18(1) and 17.
- **For iI.** Suppose Uᵢ ⊨ ψ. By compactness (Theorem 3(4)), χ ≡ σ₁ → ⋯ → σₙ → ψ is valid for
  some σₖ ∈ Uᵢ.
  - *The key step.* **χ is a valid sentence, so χ = χˢ ∈ AV ⊆ Uᵢ.** Closure then gives Tᵢχ ∈ Uᵢ,
    and also Tᵢσₖ ∈ Uᵢ for each k.
  - Repeated i-Deduction then gives Uᵢ ⊨ Tᵢψ. ∎

The paper's proof of Lemma 19 obtains Tᵢχ from i-Validity. AV already puts the valid *sentence* χ
into Uᵢ, and closure supplies Tᵢχ. So i-Validity is used only to make i-Validity itself true in
$M_U$. That is why Lemma 19 needs it in its own bundle, but introspection does not need it.

# Proposition 2. Without i-Deduction, genericity fails

The family is F = [AV]ᵢ ∪ [iV]ᵢ ∪ [iI]ⱼ (or anything smaller). Take the least closed family U ⊇ F,
so Uᵢ is the Tᵢ-closure of AV ∪ iV, plus iI if i = j.

**The countermodel.** Let X be the closure of Uᵢ ∪ {χˢ : χ valid} under σ ↦ Tᵢσ, taken up to
alphabetic variants. Let M have standard first-order part, interpret Tᵢφ[s] as "φˢ ∈ X", and
interpret every other operator similarly by its own theory.

This is a legitimate base-logic structure. Its truth value depends only on φˢ, which gives
conditions 1 and 2. And (φ(x|y))ˢ = φ^{s(x|s(y))}, which gives condition 3. Check that M ⊨ Uᵢ:
- *Substitution.* M interprets formulas by substitution, so M ⊨ AV (as in Lemma 8 / 18(1)).
- *i-Validity.* M ⊨ ucl(Tᵢχ) for χ valid, since χˢ ∈ X.
- *Closure members.* M ⊨ Tᵢσ for σ ∈ Uᵢ, since σ ∈ X, and likewise for iterates.
- *Introspection.* The iI instances hold, since X is closed under Tᵢ.

**The failure.** Let ψ ≡ Tᵢ(0=0) ∧ Tᵢ(1=1).
- Uᵢ ⊨ ψ, since both conjuncts are iV instances.
- But ψ ∉ X: it is not in Uᵢ, not an instance of a valid formula (its atoms are free), and not of
  the form Tᵢσ. So M ⊭ Tᵢψ, hence Uᵢ ⊭ Tᵢψ.
- By the criterion above, $M_U$ ⊭ i-Introspection. ∎

# Proposition 3. Without AV, genericity fails

- **If iV is kept** ([iV]ᵢ ∪ [iD]ᵢ ∪ [iI]ⱼ): the iV part is already false in $M_U$. Take k ≠ i and the
  χ above. Then ucl(Tᵢχ(x)) ∈ Uᵢ, but $M_U$ ⊨ Tᵢχ[x ↦ n] needs Uᵢ ⊨ χ(n). Here is a model of Uᵢ
  falsifying χ(n):
  - make Tᵢφ[s] true for every φ and s, which satisfies iV, iD, iI and all closure members;
  - make Tₖφ[s] true unless φ is literally θ(n).

  This respects Definition 2, whose condition 3 concerns variables only. In it Tₖθ(y)[y ↦ n] is
  true while Tₖθ(n) is false, so χ(n) fails. Hence Uᵢ ⊭ χ(n).
- **If iV is also dropped** ([iD]ᵢ ∪ [iI]ⱼ, or [iI]ⱼ alone): take the least closed U.
  - Uᵢ ⊨ 0=0, trivially.
  - Let D be the closure of Uᵢ under modus ponens and under σ ↦ Tᵢσ. Uᵢ contains only iD instances,
    Tᵢ-prefixed formulas, and iI instances if i = j. So every member of D is a Tᵢ-formula or an
    implication between such, and **(0=0) ∉ D**.
  - The model Tᵢφ[s] :⟺ φˢ ∈ D satisfies:
    - the iD instances, because D is closed under modus ponens;
    - the closure members;
    - the iI instances, because D is closed under Tᵢ.

    But it makes Tᵢ(0=0) false, so Uᵢ ⊭ Tᵢ(0=0).
  - Introspection fails at φ = (0=0). ∎

# Corollary

Among the subsets of {AV, iV, iD} placed in theory i, those making [·]ᵢ ∪ [iI]ⱼ closed-r.e.-generic
are exactly those containing **AV and iD**: {AV, iD} and {AV, iV, iD}. The unique minimal one is
{AV, iD}.

# Scope, and the second question

- The analysis covers Lemma 19's schemas only. With other schemas in the pool (Peano arithmetic,
  SMT, the Tⱼφ (φ ∈ Tⱼ) schema) there could be other minimal bundles.
  **Conjecture G1:** none of Corollary 23's other blocks can replace AV or iD for introspection.
- The stratified analogue (Lemma 64 / Corollary 71) should admit the same reduction: drop the
  validity schema, keep assigned validity and deduction. It was not checked here.
- The paper's second question, how far the stratified generic construction can be strengthened, is
  open-ended and untouched.
