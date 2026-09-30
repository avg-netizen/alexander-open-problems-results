---
title: "Knowing everyone's truthfulness, one's own mechanicalness and one's subordinates' codes"
subtitle: "A proposed affirmative answer to Question 3-1-2 of S. A. Alexander, *The Theory of Several Knowing Machines* (2013)"
date: "30 September 2026"
---

**Status.**
- **This is a proposed resolution.** It is a long hand proof, not machine-checked and without
  independent human review.
- **Checks so far:** one AI system wrote the construction; a second re-derived every step and
  wrote out the two lemmas the draft only sketched (§2, Lemmas A and B).
- **For a reader,** the key new points are the transparent stratification (§2), the
  contextual-collapse schema (§3, §6) and the induction G(i) (§5, §7).
- **Priority:** targeted searches found no earlier resolution. That is not a full priority check.

**Source.** S. A. Alexander, *The Theory of Several Knowing Machines*, doctoral dissertation,
Ohio State University, 2013 (OhioLINK ETD
[osu1366362999](https://etd.ohiolink.edu/acprod/odb_etd/ws/send_file/send?accession=osu1366362999&disposition=inline)):
- Definition 1.1.1;
- the ordinal theorem, Theorem 2.1.3, which is due to T. J. Carlson, *Knowledge, machines, and the
  consistency of Reinhardt's strong mechanistic thesis*, Ann. Pure Appl. Logic 105 (2000) 51–82;
- the stratification method of §§2.2–2.5.

**The question.** Let R be an r.e. well-founded relation on ℕ, where j R i means j is subordinate
to i. Question 3-1-2 asks whether it is consistent with self-doubting Epistemic Arithmetic that
every agent i:
- knows the truthfulness of everyone, $K_i\,\mathrm{ucl}(K_jφ→φ)$ for all j and φ;
- knows codes for its subordinates, $∃e\,K_i∀x(K_jφ↔x∈W_e)$ for j R i; and
- knows its own mechanicalness and that of its subordinates, $K_i∃e∀x(K_jφ↔x∈W_e)$ for j = i and
  for j R i.

The dissertation proves only the variant (3-1-2)′ (its Theorem 2.5.11). There, knowledge of a
non-subordinate's truthfulness is restricted to formulas in which $K_i$ is not exposed. Note 16
of this repository records a gap in the printed proof of that theorem. The theorem below implies
it.

**Answer (proposed).** **Yes**, for every r.e. well-founded R, with a uniformly r.e. family. In
it each machine also knows its own truthfulness. Knowledge of the subordinates' mechanicalness
follows from knowledge of their codes.

# 1. Background

We use the base logic, the notation φ^s, consequence ⊨ and intended structures exactly as in
note 14 §1.

**Ordinals.** The following is Theorem 2.1.3 of the dissertation, from Carlson (2000).
- For ordinals, α ≤₁ β iff α ≤ β and, for all finite X ⊆ α and finite Y ⊆ [α,β), there is a
  finite Ỹ with X < Ỹ < α and $X∪\tilde Y\cong X∪Y$ as structures for (≤, ≤₁).
- There is a recursive ordinal κ > 0 such that ≤ and ≤₁ are recursive on κ·ω, and κ·m ≤₁ κ·n
  whenever 0 < m ≤ n < ω.

# 2. Transparent i-stratification

Fix an agent i.

**The language.** $L_i$ extends $L_ω$ by operators $K_i^α$ for α < κ·ω; the unstratified $K_i$
stays in the language.

**Stratified formulas.**
- A formula is **i-stratified** if two conditions hold. First, it contains no unstratified $K_i$.
  Second, whenever $K_i^β$ occurs anywhere inside the argument of $K_i^α$, **including inside the
  argument of another operator $K_k$ (k ≠ i)**, we have β < α.
- The other operators are unstratified but *transparent*: their arguments may contain indexed
  $K_i$. The dissertation's i-stratified formulas do not allow indices under other operators.
- A formula is **very i-stratified** if every index is a positive multiple of κ.
- **Erasure** θ⁻ replaces every $K_i^α$ by $K_i$, at every depth.

**Shapes and stratifiers.**
- The *shape* of a formula is obtained by replacing every variable occurrence and every term by a
  placeholder. Alphabetic variants, and numeral or variable substitution instances, share a
  shape.
- A **(partial) shape assignment** b is a function from a set S of shapes of formulas $K_iψ$ to
  ordinals below κ·ω. It must satisfy two conditions:
  - S is closed under *$K_i$-subshapes*: the shapes of occurrences $K_iχ$ lying anywhere inside ψ,
    including under other operators;
  - b(σ) > b(σ′) for every proper $K_i$-subshape σ′ of σ.
- If b is defined on the $K_i$-shapes of an original formula φ, then $φ^b$ replaces each occurrence
  $K_iψ$ by $K_i^{b(\mathrm{shape}(K_iψ))}ψ^b$, recursively, also under other operators.
- A *stratifier* is a total computable shape assignment.
- The **height stratifier** h sets $h(σ)=κ·(1+d(σ))$, where d(σ) is the nesting depth of $K_i$
  in σ. It is very.

**Properties** (immediate from the definitions):
- (i) $φ^b$ is i-stratified;
- (ii) $(φ^b)^-=φ$;
- (iii) $φ↦φ^b$ commutes with renaming bound variables, with substituting variables for variables
  (substitutability is preserved), and with numeral instances: $(φ^s)^b=(φ^b)^s$;
- (iv) if β is an order-isomorphism between finite sets of ordinals, then β∘b is again an
  assignment.

**Lemma A (extension).** Let b be a finite assignment with values below a limit ordinal λ ≤ κ·ω.
Then b extends to a stratifier with all values below λ.

*Proof.* Enumerate all shapes of $K_i$-formulas in order of size. For each new shape σ, set
b(σ) = 1 + max{b(σ′): σ′ a proper $K_i$-subshape of σ}, which is defined, or 0 if σ has none.
- Subshapes are smaller, so they have already been assigned.
- The value stays below λ because λ is a limit.
- Computability holds because the ordinal notation is recursive. □

**Lemma B (validity transfer).**
- (1) If Φ is a valid $L_ω$-formula and b is a stratifier, then $Φ^b$ is valid.
- (2) If Ψ is a valid $L_i$-formula containing no unstratified $K_i$, then $Ψ^-$ is valid.

*Proof.*
- (1) Let N be any $L_i$-structure. Define an $L_ω$-structure N″ with the same first-order part:
  $N″⊨K_iψ[s]$ iff $N⊨(K_iψ)^b[s]$, and $N″⊨K_kψ[s]$ iff $N⊨K_kψ^b[s]$ for k ≠ i.
  - N″ is a structure. Free variables are preserved by b. Alphabetic variants go to alphabetic
    variants, and substitution of variables commutes with b, by (iii). So the three conditions of
    Definition 1.2.3 transfer from N.
  - Induction on formulas gives $N″⊨χ[s]$ iff $N⊨χ^b[s]$.
  - Since Φ is valid, N″ ⊨ Φ, hence N ⊨ $Φ^b$.
- (2) Given an $L_ω$-structure N, define N′ by $N′⊨K_i^αψ[s]$ iff $N⊨K_iψ^-[s]$, and
  $N′⊨K_kψ[s]$ iff $N⊨K_kψ^-[s]$. Erasure commutes with renaming and substitution, so N′ is a
  structure, and $N′⊨χ[s]$ iff $N⊨χ^-[s]$. □

# 3. The theories

A **one-hole context** C[·] is a formula with one distinguished subformula position, possibly
under quantifiers, connectives, indexed $K_i$, or other operators $K_k$.

For each agent i and parameter n, let $Σ_i(n)$ consist of the universal closures of the following
i-stratified formulas.

1. **Strativalidity:** $K_i^αθ$ for valid θ.
2. **Stratideduction:** $K_i^α(θ→ψ)→K_i^αθ→K_i^αψ$.
3. **Stratrospection:** $K_i^αθ→K_i^βK_i^αθ$ for α < β.
4. **PA:** the PA axioms, with induction for i-stratified formulas.
5. **Assigned Validity:** $θ^s$ for valid θ.
6. **Own stage truth:** $K_i^αθ→θ$.
7. **Other-agent truth:** $K_kθ→θ$ for k ≠ i. Here θ is any i-stratified formula; θ may expose
   $K_i^α$.
8. **Own stage mechanicalness:** $∃e∀x(K_i^αθ↔x∈W_e)$ for θ with $FV(θ)=\{x\}$.
9. **Contextual collapse (CC):** $C[K_i^αθ]↔C[K_i^βθ]$ for α ≤₁ β.
10. **Subordinate codes:** for j R i, every original φ with $FV(φ)=\{x\}$, and every finite
    assignment b on the $K_i$-shapes of φ,
    $$∀x\,(K_jφ^b↔x∈W_{c(n,j,φ)}),\qquad W_{c(n,j,φ)}=\{m:⟨\ulcorner φ\urcorner,j,m⟩∈W_n\}.$$
    The index depends only on the **original** φ, not on b.
11. **Prefix closure:** $K_i^ασ$ for every σ generated by items 1–11 whose indices are all
    below α.

Let $T_i(n)=Σ_i(n)^-$. Both families are uniformly r.e., since R is r.e. and κ·ω is recursive.

**The fixed point.** By the recursion theorem, choose q so that $W_q$ is the set of triples
$⟨\ulcorner φ\urcorner, j, m⟩$ with $FV(φ)=\{x\}$ and $T_j(q)⊨φ(x|\bar m)$. Write $Σ_i,T_i$ for $Σ_i(q),T_i(q)$.
Then

$$m∈W_{c(q,j,φ)}\iff T_j⊨φ(x|\bar m).\tag{1}$$

Let $Σ_i∩α$ be the set of axioms of $Σ_i$ all of whose indices are below α.

**The erased theory contains everything asked for.**
- **Truthfulness:** $T_i$ contains unrestricted reflection for every agent. Items 6 and 7 erase to
  $K_jφ→φ$ for **every** original φ, using the lift $φ^h$.
- **Codes:** $T_i$ contains the particular codes of item 10.
- **Own mechanicalness:** item 8, applied to $θ=φ^h$, erases to self-mechanicalness.
- **The EA axioms and their known versions:** these come from items 1–5 and 11. Lemma B(1) gives a
  valid lift of every original validity, and item 11 supplies the $K_i$-prefixes.

# 4. Syntactic lemmas (no soundness assumed)

**Uniformity.** If β is a (≤,≤₁)-isomorphism between finite sets of ordinals, applying β to the
indices of a generator gives a generator. Each schema needs checking:
- the side conditions α < β and α ≤₁ β are preserved;
- a renamed valid formula is valid, by renaming the interpretations;
- in item 10, β∘b is an assignment (property iv) and the index is unchanged;
- item 11 follows by induction.

**(5) Finite-support collapse.** If α ≤₁ β and θ is i-stratified with all indices below α, then
$Σ_i∩α⊨θ$ iff $Σ_i∩β⊨θ$.
- *Proof.* Take finitely many premises from $Σ_i∩β$. Let X be their indices below α together with
  those of θ, and let Y be the premises' indices in [α,β). Choose Ỹ as in the definition of ≤₁, and
  apply the isomorphism X∪Y → X∪Ỹ, which fixes X.
- The renamed premises are generators (uniformity) with indices below α. The implication stays
  valid, and θ is unchanged. □

**Very counterparts.** Mapping the finite set of indices of a generator order-preservingly onto
positive multiples of κ gives a very generator with the same erasure. All the side conditions are
"positive" (<, ≤₁), and they hold among κ-multiples.

**(6) Equivalence of very lifts.** If ρ and σ are very i-stratified and ρ⁻ = σ⁻, then
$Σ_i⊨\mathrm{ucl}(ρ↔σ)$.
- *Proof.* ρ and σ have the same formula tree. Fix target labels $κ·N_p$ on the positions p of
  $K_i$-occurrences. Every $N_p$ exceeds all indices of ρ and σ, and $N_p$ decreases strictly
  along nesting.
- Change ρ's labels one occurrence at a time, outermost first.
  - Every intermediate formula is i-stratified: ancestors already carry larger targets, and
    descendants still carry smaller old labels.
  - Each step is a CC instance, since κ·a ≤₁ κ·N_p.
- Do the same for σ, and chain the biconditionals. □

This holds inside other operators because CC allows holes there. It does **not** need $Σ_i$ to
contain another agent's deduction axioms.

**(7) Proof stratification.** For very i-stratified sentences θ, $Σ_i⊨θ$ iff $T_i⊨θ^-$.
- **(⇒)** Erase a valid implication from premises in $Σ_i$ (Lemma B(2)).
- **(⇐)**
  - Start from a valid $σ_1^-→\dots→θ^-$ with each $σ_l∈Σ_i$.
  - Its height lift is valid (Lemma B(1)), with very components $(σ_l^-)^h$ and $(θ^-)^h$.
  - Replace each $(σ_l^-)^h$ by the very counterpart of $σ_l$, and $(θ^-)^h$ by θ, using (6). □

**(8) Prefix.** If $Σ_i∩α⊨θ$ for a sentence θ, $K_i^αθ$ is i-stratified, and β > α, then
$Σ_i∩β⊨K_i^αθ$. This uses item 11 on the premises, item 1 on the implication, and item 2.

# 5. The provisional structures and the induction

Let P = (P_k) be predicates on closed $L_ω$-sentences that are invariant under alphabetic
variants. Define $F_P$, on standard arithmetic, by recursion on formula complexity:

$$F_P⊨K_kθ[s]\iff P_k(θ^s)\ \text{and}\ F_P⊨θ[s].\tag{9}$$

$F_P$ is a structure and is numeral-instance invariant, as in note 14. Let $D_i$ consist of i and
every agent reachable from i by a finite descending R-path. We prove by well-founded induction:

> **G(i).** For every such P with $P_k(σ)⟺T_k⊨σ$ for all $k∈D_i$, we have $F_P⊨T_i$.

Nothing is assumed about $P_k$ for k ∉ $D_i$.

Fix i, assume G(j) for every j R i, and fix P as in G(i). Expand $F_P$ to $L_i$ as M:

$$\begin{aligned}
M⊨K_kθ[s]&\iff P_k((θ^-)^s)\ \text{and}\ M⊨θ[s]\qquad(k∈ℕ,\ \text{unstratified }K_k),\\
M⊨K_i^αθ[s]&\iff Σ_i∩α⊨θ^s\ \text{and}\ M⊨θ[s].
\end{aligned}\tag{10}$$

On $L_ω$ this is exactly $F_P$. The erasure in the first clause matters: the raw predicate sees
the same argument whatever the indices. M is a numeral-invariant structure.

# 6. Contextual collapse is true in M

We claim that M ⊨ ucl(C[K_i^αθ] ↔ C[K_i^βθ]) whenever α ≤₁ β and both sides are i-stratified. The
proof is by induction on the context C.
- **Empty context:** the consequence conditions agree by (5), and the truth conditions are
  identical.
- **Connectives and quantifiers:** immediate from the induction hypothesis.
- **Context $K_kC′$ with k ≠ i:** both arguments have the same erasure, so the $P_k$ conditions in
  (10) coincide. The truth conditions agree by induction.
- **Context $K_i^γC′$:** both sides are i-stratified, so α, β and all indices of C′ are below γ.
  - The CC instance for C′ lies in $Σ_i∩γ$, and Assigned Validity yields its numeral instances.
    So $Σ_i∩γ$ proves one argument's numeral instance iff it proves the other's.
  - The truth conditions agree by induction.

No soundness of $Σ_i$ is used here.

# 7. Subordinate codes, by rebuilding the truth filters

Fix j R i, an original φ with FV(φ) = {x}, and a finite assignment b.
- **The reconstructed predicate.** Extend b to a stratifier g (Lemma A with λ = κ·ω). Define
  $Q_k=P_k$ for k ≠ i and $Q_i(θ)⟺M⊨(K_iθ)^g$. By (iii), $Q_i$ is invariant under alphabetic
  variants.
- **The rebuilt structure.** Let N = $F_Q$. **Every** truth filter is rebuilt; none is frozen.

**Claim.** For original θ, $N⊨θ[s]\iff M⊨θ^g[s]$. The proof is by induction.
- For $K_kθ$ with k ≠ i: the raw tests agree because $(θ^g)^-=θ$, and the truth tests agree by
  induction.
- For $K_iθ$: $N⊨K_iθ[s]$ iff $M⊨(K_iθ)^g[s]$ and $M⊨θ^g[s]$, using (iii) and numeral invariance.
  The second conjunct is implied by the first, since $(K_iθ)^g=K_i^{g(\cdot)}θ^g$ is factive
  in M.

R is well-founded, so i ∉ $D_j$ ⊆ $D_i$. Q therefore agrees with the proof predicates on $D_j$, and
G(j) gives N ⊨ $T_j$. Hence, by the claim and (1),

$$M⊨K_jφ^b[x↦m]\iff N⊨K_jφ[x↦m]\iff T_j⊨φ(x|\bar m)\iff m∈W_{c(q,j,φ)}.$$

So every item-10 axiom is true in M. The unchanged predicates for $D_j$ are *proved* correct in the
rebuilt structure by G(j). No lemma that freezes other operators is used; compare note 16.

# 8. Stage soundness

We show M ⊨ $Σ_i∩α$ by induction on α < κ·ω.
- **Items 1–5:** validity, modus ponens, (8) with the truth half, standard arithmetic, and numeral
  invariance.
- **Items 6 and 7:** the truth halves of (10).
- **Item 9:** §6.
- **Item 10:** §7.
- **Item 8 at β < α:** by induction $Σ_i∩β$ is sound, so the extension of $K_i^βθ$ is
  $\{m:Σ_i∩β⊨θ(\bar m)\}$, which is r.e.
- **Item 11 at β < α:** σ ∈ $Σ_i∩β$ is proved, and it is true by induction.

Hence M ⊨ $Σ_i$.

# 9. Erasure, and the end of the proof

**Claim.** For every very i-stratified θ, $M⊨θ[s]\iff M⊨θ^-[s]$. The proof is by induction.
- At $K_kψ$, the raw tests coincide and the truth tests agree by induction.
- At $K_i^{κn}ψ$:
  - by cofinality and (5), $Σ_i∩κn⊨ψ^s$ iff $Σ_i⊨ψ^s$;
  - by (7), this holds iff $T_i⊨(ψ^-)^s$, which is $P_i$ since i ∈ $D_i$;
  - the truth conjuncts agree by induction.

  So the clause coincides with the one for $K_iψ^-$.

This identity is syntactic apart from the inductive truth conjunct.

**Conclusion of G(i).** Every axiom of $T_i$ is the erasure of a generator with a very
counterpart. That counterpart is true in M, so the erased axiom is true in M, hence in $F_P$. So
$F_P⊨T_i$, which is G(i).

**The theorem.** Take $P_k$ to be $T_k$-provability for every k. Then G(i) holds for every i, so
every filter is redundant, and $F_P$ is the intended structure of the uniformly r.e. family.
§3 lists the required contents of $T_i$.

**Theorem (proposed).** For every r.e. well-founded R there is a uniformly r.e. family of knowing
machines satisfying self-doubting Epistemic Arithmetic, together with:
- unrestricted mutual truthfulness;
- known particular codes of subordinates;
- known own mechanicalness.

In particular, Question 3-1-2 has the answer yes. ∎

# 10. Remarks

- **Why this does not settle 3-1-3.** Question 3-1-3 also asks for knowledge of the
  mechanicalness of **non-subordinates**. G(i) is proved for *arbitrary* external predicates, and
  under such predicates an external mechanicalness axiom can be false. For example, if $P_k$
  accepts every sentence, its filtered column on x∉$W_x$ is the non-r.e. nonhalting set. 3-1-3
  remains open.
- **The two ingredients that make exposed reflection possible.**
  - *Transparency:* indices may occur under other operators, and other operators test the erased
    argument. This makes item 7 free of charge even when $K_i$ is exposed.
  - *Contextual collapse:* CC erases to tautologies, so it gives no machine another machine's
    private code axioms, and it is proved true directly in §6.
