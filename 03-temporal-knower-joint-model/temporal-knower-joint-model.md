---
title: "A joint model for the surprise examination and temporal knower sentences"
subtitle: "On the concluding conjecture of Aldini, Alexander and Graziani, *Knowledge-of-own-factivity, the definition of surprise, and a solution to the Surprise Examination paradox*"
date: "21 September 2026"
---

**Status.** A proposed resolution, by a complete hand argument. Independent review and external
priority checking remain. No proof-assistant check has been run.

**Source.** A. Aldini, S. A. Alexander and P. Graziani, *Knowledge-of-own-factivity, the
definition of surprise, and a solution to the Surprise Examination paradox*, CIFMA 2022,
Springer LNCS, 2023. [doi:10.1007/978-3-031-26236-4_30](https://doi.org/10.1007/978-3-031-26236-4_30).
The text examined is the 17-page conference pre-proceedings version
([PDF](https://cifma.github.io/Papers-2022/CIFMA_2022_paper_Aldini.pdf)).

**What is shown.** The paper conjectures that its temporal theory of knowledge can be extended by
self-referential sentences $L_i$ ("this sentence is known at time $i$ to be false"). It further
asks that every later time knows the falsehood of every earlier $L_i$, and that the whole remain
consistent. A model is constructed. It preserves:
- factivity, retention and deduction;
- knowledge of logical validities;
- delayed knowledge of factivity;
- stratified closure.

It adds the non-atomic sentences $L_i$ with their exact semantics, and satisfies the stronger
demand. This is not a Kripke/S4 model.

**Contribution.** The paper's §5 construction supplies the main method. What is new here is:
- the extension to its proposed self-referential language;
- an explicit closure argument;
- the observation that the additional delayed-knowledge condition follows automatically (§2).

Check script: `temporal_knower_controls.py` in this folder, which writes
`temporal_knower_controls.json`.

# 1. Language and the semantic point that matters

Fix an examination window of $n\ge3$ days. First use active temporal indices
$I=\{1,\ldots,n\}$. As in the source, the **language** still has $D_i$ and
$K_i$ for every positive integer $i$, together with the usual Boolean
connectives and the new non-atomic $L_i$ for every positive $i$. Only the
outer temporal indices of the theory's schemas are restricted to $I$;
their formula parameters may mention indices beyond the examination window.

Following the paper, a model freely assigns truth values to basic formulas
$D_i$ and $K_i\varphi$. It evaluates Boolean connectives classically, and
the added clause is

$$M\models L_i\quad\Longleftrightarrow\quad M\models K_i\neg L_i.$$

This is well-defined: $K_i\neg L_i$ is a **basic formula** with an assigned
truth value. Evaluating it does not recursively evaluate its argument. In
particular, $L_i$ is neither an independently valued propositional atom nor
a string to be expanded infinitely inside every modality.

For precision, translate each $K_i\varphi$ to a distinct propositional atom
$a_{i,\varphi}$, each $D_i$ to $d_i$, and $L_i$ to $a_{i,\neg L_i}$;
translate Boolean connectives homomorphically. This translates satisfaction
exactly to ordinary propositional satisfaction. Consequently semantic
consequence is compact, has the usual finite-premise deduction property,
and includes the validity $L_i\leftrightarrow K_i\neg L_i$. These are
validities of the expanded semantics, as required by the source's definition
of tautology. All schemas below range over the **expanded** language.

Write $\operatorname{Cn}(T)$ for semantic consequence in this language, and
$F_i=\{K_i\varphi\to\varphi:\varphi\text{ any formula}\}$ for the factivity
schema at time $i$.

# 2. The stronger delayed-knowledge condition is automatic once consistency holds

Put $q_i=(K_i\neg L_i\to\neg L_i)$. By the semantic clause,

$$q_i\to\neg L_i$$

is valid: if $L_i$ were true, both $K_i\neg L_i$ and $L_i$ would be true,
making $q_i$ false. Any factive model satisfies $q_i$, hence $\neg L_i$.

If $j>i$, delayed knowledge of factivity includes $K_jq_i$. Knowledge of
validities gives $K_j(q_i\to\neg L_i)$, and closure under modus ponens gives

$$K_j\neg L_i.$$

Thus the additional conjectural requirement follows from the proposed
semantics and existing schemas. The main problem is producing a joint model
of those schemas; no extra axiom asserting $K_j\neg L_i$ is needed.

# 3. Spell out the stratified theories

Let $S$ contain the following source axioms, with all indicated formulas in
the expanded language:

1. $\bigvee_{i=1}^nD_i$, and $\neg(D_i\wedge D_j)$ for $1\le i<j\le n$.
2. The paper's broadened surprise assertion
   $$\bigvee_{i=1}^n(D_i\wedge\neg K_iD_i)
     \ \vee\!\bigvee_{1\le i<j\le n}(D_i\wedge K_iD_j).$$
3. $\neg D_i\to K_{i+1}\neg D_i$ for $i<n$.
4. $K_i\varphi$ for each valid $\varphi$ and $i\in I$.
5. $K_i(\varphi\to\psi)\to(K_i\varphi\to K_i\psi)$.
6. $K_i\varphi\to K_j\varphi$ for $i<j$.
7. $K_j(K_i\varphi\to\varphi)$ for $i<j$.

For $J\subseteq I$, let $\operatorname{Cl}_J(T)$ be the **least** theory
containing $T$, closed under semantic consequence and under
$\varphi\mapsto K_j\varphi$ for each $j\in J$. Such a theory exists by
intersection of all closed supersets. Compactness also permits construction
by iterating the closure operations through finite stages and taking their
union. This is a definition of sets of formulas, not a claim that their
membership or semantic consequence is decidable.

Define

$$B_0=\operatorname{Cl}_I(S),\qquad
B_i=\operatorname{Cl}_{\{i\}}\left(B_{i-1}\cup\bigcup_{r<i}F_r\right)
\quad(1\le i\le n).$$

In particular $B_1=B_0$. These are the deductively closed presentations of
the paper's $(V_n)_0$ and $(V_n)^i_0$ in the expanded language. Closing under
consequence changes no models. To check the correspondence, the new part of
stage $i$ is precisely past factivity and knowledge, at time $i$, of that
stage's consequences. The lower-time closure clauses are already included
in $B_{i-1}$. Thus $B_i\subseteq B_j$ for $i<j$, and whenever
$B_i\models\varphi$, $K_i\varphi\in B_i$.

The desired full theory is

$$V_n^L=\bigcup_{i=1}^nB_i\ \cup\!\bigcup_{i=1}^nF_i.$$

The final factivity schemas are **not** placed inside every earlier knowledge
closure. Doing so would change the theory and restore the knower obstruction.

# 4. One auxiliary model proves the needed ignorance

Take the actual exam to be on day 1. To ensure it is not known beforehand,
we first show $B_0\not\models D_1$.

Define $N$ by making $D_2$ true and every other $D_i$ false, and assigning
**every** basic $K_i\varphi$ truth value true. The added semantic clause
therefore makes every $L_i$ true. It would be an error to declare these $L_i$
false while keeping all knowledge formulas true.

$N$ satisfies $S$. The examination is unique. The second surprise disjunction
has the witness $D_2\wedge K_2D_3$, available because $n\ge3$. The observation,
deduction, retention, knowledge-of-validity and delayed-factivity clauses
hold because all their modal conclusions are true. Moreover every formula
added by a knowledge-closure rule is true in $N$, and semantic consequence
preserves truth in $N$. Hence $N\models B_0$, but $N\not\models D_1$.

The auxiliary model is deliberately nonfactive. It witnesses non-entailment
by a theory that has not yet assumed current/future factivity. It is not the
final model and does not weaken the final factivity requirement.

# 5. The actual model

Let

$$H_i=\{\neg D_j:1\le j<i,\ j\ne1\},\qquad W_i=B_i\cup H_i.$$

The $W_i$ are nested. Assign the basic truth values of $M$ by

$$M\models D_j\quad\Longleftrightarrow\quad j=1,$$
$$M\models K_i\varphi\quad\Longleftrightarrow\quad W_i\models\varphi,
\qquad i\in I.$$

For positive $i\notin I$, assign every basic $K_i\varphi$ false. This completes
the valuation on the full source language. The finite-window theory imposes
no factivity or closure schemas at those outer indices, though formulas
containing them remain available inside all active-index schemas.

The truth values of the $L_i$ are supplied by their semantic clause, not
chosen separately. All theories on the right were defined before $M$; this
is a mathematical model definition, not an effective evaluation algorithm.

First verify $M\models S$:

- The exam is unique. Since $W_1=B_1=B_0\not\models D_1$, the surprise
  witness is $D_1\wedge\neg K_1D_1$.
- If $M\models\neg D_j$, then $j\ne1$ and $\neg D_j\in H_{j+1}$, giving
  the observation clause.
- Valid formulas are consequences of every $W_i$. Semantic consequence is
  closed under modus ponens, giving modal deduction.
- $W_i\subseteq W_j$ gives retention.
- If $r<i$, then $F_r\subseteq B_i\subseteq W_i$. Thus
  $M\models K_i(K_r\varphi\to\varphi)$, giving delayed factivity.

Every application of a knowledge-closure rule while forming $B_0$ introduces
a true formula in $M$: for all
$i$, $W_i$ contains $B_0$, so $B_0\models\varphi$ implies
$M\models K_i\varphi$. Together with $M\models S$, closure induction
gives $M\models B_0$.

Now prove $M\models B_i$ and $M\models W_i$ by induction on $i$. All $H_i$
are true under the chosen actual exam date. Suppose the earlier $W_r$ are
true in $M$. For each $r<i$, if $M\models K_r\varphi$, the definition says
$W_r\models\varphi$; because $M\models W_r$, it follows that
$M\models\varphi$. Thus $M\models F_r$ for every $r<i$.

The seeds $B_{i-1}\cup\bigcup_{r<i}F_r$ of $B_i$ therefore hold in $M$.
Any formula $K_i\varphi$ introduced by its knowledge-closure rule is also true:
$B_i\models\varphi$ implies $W_i\models\varphi$ by inclusion. Closure
induction gives $M\models B_i$, and the true histories give
$M\models W_i$. This argument does not assume current factivity to prove
current soundness: only earlier $W_r$ are used in the factivity step.

Finally, for every $i$ and $\varphi$, if $M\models K_i\varphi$, then
$W_i\models\varphi$ and $M\models W_i$, hence $M\models\varphi$.
Therefore $M$ is factive at every time and satisfies $V_n^L$.

By §2 it also satisfies, for every $i<j\le n$,

$$\neg L_i,\qquad \neg K_i\neg L_i,\qquad K_j\neg L_i.$$

The middle statement follows from the defining equivalence and $\neg L_i$.
The additional later-knowledge conjecture is thus satisfied in the same model.

# 6. All positive times, and the exact boundary of the result

If “whenever $i<j$” is intended to quantify over **all positive times**, the
same construction works. Keep the examination window $1,\ldots,n$ with
$n\ge3$, but take $I=\mathbb N_{>0}$. Include deduction, retention,
knowledge of validities and delayed factivity for all temporal indices,
and observation $\neg D_i\to K_{i+1}\neg D_i$ for every positive $i$.
Define $B_i,H_i,W_i$ for each finite $i$ and take the union of all $B_i$ and
all $F_i$ as the final theory. Use the same $N$ and $M$, with all $D_j$
except the chosen examination day false, including days beyond the window.
Every argument above is indexed by a finite $i$ and remains valid. This gives
$K_j\neg L_i$ for all positive $i<j$, with an examination still held within
the original finite window. This is a stated stronger temporal extension,
not a silent change to the paper's finite-window theory.

For $n=1,2$ the source already proves its original theory inconsistent.
Those derivations use only the original language and remain available here;
the extension does not repair them. The threshold of three days is inherited
from the source, not a new result claimed by this note.

Adding $K_iq_i$, knowledge at time $i$ of its own particular factivity instance,
would be inconsistent with these requirements. The validity
$q_i\to\neg L_i$, known deduction and $K_iq_i$ would give $K_i\neg L_i$,
therefore $L_i$, contradicting factivity. The proof identifies the missing
knowledge precisely; it does not abandon actual factivity or retention.

# Verification and source limits

The script checks:
- the special semantic translation;
- the short derivation from factivity to falsehood;
- the obstruction from same-time knowledge of factivity;
- finite instances in the all-knowing auxiliary valuation.

It also includes a negative control showing why setting the new sentences false independently
breaks the auxiliary model. These finite tests do not check the infinite theory closures; §§3–5
supply that hand argument.

The source's Definition 4 was inspected visually on printed p. 10. Its §5 proof and concluding
conjecture on p. 16 were read. A targeted public search on 21 September 2026 did not locate a
later explicit solution of this joint-model conjecture. No comprehensive citation search was
available, so priority is unresolved.

# References

- A. Aldini, S. A. Alexander, P. Graziani, as above (Definition 4, §5, and the concluding
  conjecture).
