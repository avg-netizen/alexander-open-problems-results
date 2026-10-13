---
title: "A counterexample to Lemma 2.5.5 of *The Theory of Several Knowing Machines*"
subtitle: "A gap in the printed proof of the dissertation's answer to Question (3-1-2)′"
date: "30 September 2026"
---

**Status.**
- **Kind of result:** an explicit countermodel, checked against the rendered PDF of the
  dissertation. It was found by one AI system and verified by another. No independent human
  review.
- **Scope:** it refutes the lemma as printed. It does **not** refute the theorem the lemma
  supports. That theorem follows from the proposed result of note 15.

**Source.** S. A. Alexander, *The Theory of Several Knowing Machines*, doctoral dissertation,
Ohio State University, 2013 (OhioLINK ETD
[osu1366362999](https://etd.ohiolink.edu/acprod/odb_etd/ws/send_file/send?accession=osu1366362999&disposition=inline)):
Definition 2.5.4 and Lemma 2.5.5 (printed pp. 68–69), and Claim 8 of the proof of Theorem 2.5.11
(p. 76).

# The lemma

**The relation "mod_tru".** Definition 2.5.4 defines $M_1≡M_2\ \mathrm{mod}_{tru}\ j$ for
structures with standard first-order part. Among its conditions:
- (1)–(2) certain operators are interpreted identically;
- (3) $M_p⊨K_kφ→φ[s]$ for **every** k, formula φ and p ∈ {1, 2};
- (4) the same factivity for the indexed operators;
- (5) numeral-instance invariance.

**The lemma.** Lemma 2.5.5 takes a standard structure M with properties (3)–(5) and an
i-stratifier +. It forms M/i by changing **only** the interpretation of $K_i$:

$$M/i⊨K_iφ[s]\iff φ∈L_ω,\ M/i⊨φ[s],\ \text{and}\ M⊨(K_iφ)^+[s].$$

It asserts that $M/i≡M\ \mathrm{mod}_{tru}\ j$ whenever j R i. The printed proof calls conditions
1–4 "immediate".

# Counterexample

**The model.** Take the one-edge relation 0 R 1, with j = 0 and i = 1. Let M have standard
arithmetic and be defined recursively by:
- $M⊨K_kφ[s]\iff M⊨φ[s]$ for every unstratified $K_k$;
- every indexed $K_k^α$ false everywhere.

**M satisfies the lemma's hypotheses.**
- M is a structure: independence from non-free variables, alphabetic invariance and weak
  substitution all follow by induction on formulas.
- M is numeral-instance invariant.
- Every operator is factive: the unstratified ones by definition, the indexed ones vacuously.

**The failure.** Let τ be 0 = 0.
- **In M:** $M⊨K_iτ$, and therefore $M⊨K_jK_iτ$.
- **In M/i, the changed operator:** $(K_iτ)^+$ is $K_i^ατ$ for some α, which is false in M. So
  $M/i⊭K_iτ$.
- **In M/i, the frozen operator:** the interpretation of $K_j$ is unchanged, so its value on the
  argument $K_iτ$ is still "true": $M/i⊨K_jK_iτ$.

Hence M/i violates $K_jK_iτ→K_iτ$. Condition (3) fails for j itself, contradicting the lemma. □

# Where the argument breaks, and consequences

**The cause.** Factivity of the *changed* operator follows from its new truth conjunct. Factivity
of a *frozen* operator does not: some of its previously true assertions mention $K_i$, and $K_i$'s
truth value has changed. Adding a truth filter to $K_j$ would restore factivity, but it would
change $K_j$'s interpretation, which conditions (1)–(2) require to stay fixed.

**Effect on the dissertation.** Theorem 2.5.11 applies the lemma in Claim 8 (the stratified
subordinate reflection schema). So the printed proof of the dissertation's answer to (3-1-2)′
has a gap at that step.
- The theorem's conclusion is not refuted.
- A preservation argument tailored to the constructed theories could repair it.
- The proposed proof of the stronger Question 3-1-2 in note 15 avoids this operation entirely. It
  rebuilds *every* truth filter, and then *proves* that the relevant subordinate interpretation
  is unchanged by induction. If that proof is correct, it implies Theorem 2.5.11.

**A related caution.** Rebuilding *all* truth filters is not a universal fix either. It can
destroy *mechanicalness* instead of factivity. Suppose a superior knows a code for a lower
machine's column on σ ∧ "x ∈ $W_x$", where σ is true, and the lower machine is replaced by one
that does not prove σ. Then the superior's rebuilt column on the corresponding code-certificate
instances is the nonhalting set. This is why note 15's induction quantifies over *all* external
interpretations, and why its method does not directly give Question 3-1-3.
