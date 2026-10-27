# A specified recursive witness for ill-founded self-referential theories

27 October 2026.

**Status.** Local hand proof. The exact order and fixed-point compilation
procedure are specified below. There is no independent mathematical review,
formal verification, complete implementation of the modal proof enumerator,
or claim of novelty. The construction uses ordinary effective syntax and
Alexander's published modal consequence procedure. It does not use Theorem 79
as an existence oracle, and does not use the local negative answer to 3.2.1.

## 1. The target and the source conventions

Fix Alexander's recursive language \(L=L_{\rm PA}(\omega)\), with operators
\(K_i\) for \(i\in\mathbb N\). His semantic consequence relation is denoted
\(\vdash\) here. By his Theorem 3 it is compact and the consequences of an
r.e. theory can be enumerated effectively, uniformly from its index.

For a uniformly r.e. family \(T=(T_i)\), its canonical structure has standard
first-order part and satisfies
\[
 M_T\models K_i\phi[s]\quad\Longleftrightarrow\quad
 T_i\vdash\phi^s.
\]
Here \(\phi^s\) is the sentence obtained by substituting the corresponding
numerals. Alexander's Lemma 8 verifies the substitution property. A family is
*true* when \(M_T\models T_i\) for every \(i\).

A family is *closed* when \(\sigma\in T_i\) implies \(K_i\sigma\in T_i\).
A background family \(B=(B_i)\) is *closed-r.e.-generic* when it is uniformly
r.e. and \(M_U\models B\) for every closed uniformly r.e. \(U\supseteq B\).
This is Definition 14 of the source; it does not require \(B\) itself to be
closed.

We construct one recursive strict partial order \(\prec_*\) on \(\mathbb N\)
with the following properties:

1. It is ill-founded.
2. From an enumeration index of any closed-r.e.-generic \(B\), an ordinary
   algorithm produces an index \(n\) for which the family \(T(n)\) from
   Alexander's Theorem 24, formed using \(\prec_*\), is true.

Thus the particular order below witnesses the full universal-background
statement of Theorem 79(1). The algorithm runs even for a nongeneric input;
genericity is a hypothesis of its soundness conclusion.

## 2. A sufficient condition replacing well-foundedness

Let \(A\) be the set of codes of true sentences of ordinary first-order
arithmetic. Any fixed effective coding can be used; coding changes are
computable. Write \(\leq_T A\) for computability with this set as an oracle.

**Lemma 1.** Suppose \(\prec\) is an r.e. strict partial order with no infinite
descending sequence computable from \(A\). For every closed-r.e.-generic
\(B\), the effective fixed-point construction in Theorem 24 produces a true
family on \(\prec\).

**Proof.** For each natural number \(n\), form the smallest closed family
\(T(n)\) whose \(i\)-th member contains:

- \(B_i\);
- for every \(j\) and every formula \(\phi\) with free variables contained
  in \(\{x\}\),
  \[
  \forall x\bigl(K_j\phi\leftrightarrow
  \langle\ulcorner\phi\urcorner,j,x\rangle\in W_{\bar n}\bigr);
  \tag{1}
  \]
- \(\operatorname{ucl}(K_j\phi\to\phi)\) for every \(j\prec i\) and
  every formula \(\phi\).

This family is uniformly r.e., uniformly in \(n\) and the input indices.
Use the source's uniform consequence enumeration to compute a total function
\(f\) on indices such that
\[
 W_{f(n)}=\{\langle\ulcorner\phi\urcorner,j,m\rangle:
 \operatorname{FV}(\phi)\subseteq\{x\},\quad
 T_j(n)\vdash\phi(x\mid\bar m)\}.
 \tag{2}
\]
The effective recursion theorem supplies a computably obtained \(n\) with
\(W_n=W_{f(n)}\). Put \(T=T(n)\) and \(M=M_T\). Up to here no
well-foundedness or oracle computation has been used.

Each of the first two kinds of generator is true in \(M\). For the background
this follows from genericity, since \(T\) is closed, uniformly r.e. and
extends \(B\). For (1) it follows directly from (2) and the canonical
interpretation, exactly as in Theorem 24. A generator added by closure,
\(K_i\sigma\) with \(\sigma\in T_i\), is also always true: membership gives
\(T_i\vdash\sigma\), regardless of whether \(\sigma\) itself is true.

Consequently the local induction step from the published proof holds:
\[
 \bigl(\forall j\prec i\; M\models T_j\bigr)
 \quad\Longrightarrow\quad M\models T_i.
 \tag{3}
\]
Indeed, if all subordinate theories are true, a subordinate consequence
\(\phi^s\) is true in the same structure. The substitution lemma then
verifies every subordinate truth schema in \(T_i\). This checks all
generators and their closure.

Define
\[
 D=\{i: (\exists\sigma\in T_i)\;M\not\models\sigma\}.
 \tag{4}
\]
The set \(D\) is **c.e. relative to \(A\)**, uniformly from the family
index. To see this without treating modal truth as an additional oracle,
use the translation from the proof of Theorem 79: replace an outermost modal
subformula \(K_j\psi\) by the arithmetic assertion that \(T_j\) proves the
numeral substitution instance of \(\psi\). The uniform consequence
enumerator makes that an arithmetic, indeed existentially definable,
assertion. Translate the ordinary Boolean operations and quantifiers
recursively. This computes an arithmetic sentence \(F_T(\sigma)\) with
\[
 M\models\sigma\quad\Longleftrightarrow\quad
 \mathbb N\models F_T(\sigma).
 \tag{5}
\]
Thus \(A\) decides the truth of each enumerated axiom; dovetailing enumerates
\(D\). No decision of the universal statement \(M\models T_i\) is needed.

By contraposition of (3), every \(i\in D\) has a \(j\in D\) with
\(j\prec i\). If \(D\) were nonempty, fix one \(i_0\in D\) as a natural
number parameter. Given \(i_k\), dovetail the enumeration of \(D\) with that
of \(\prec\), until some \(j\in D\) with \(j\prec i_k\) appears, and put
\(i_{k+1}=j\). The search always terminates. It defines an \(A\)-computable
infinite descending sequence, contradicting the hypothesis. Therefore
\(D=\varnothing\), which proves the lemma. \(\square\)

The fixed starting number does not require an effective search for an
unsound theory. A contradiction needs the existence of an oracle program
with that one finite parameter. Also, the search uses an enumeration of
\(D\), rather than its characteristic function: it does not silently invoke
the jump \(A'\).

## 3. An explicit recursive tree with no A-computable branch

Here is a finite algorithm for the tree; it is not an instruction to choose
an unspecified Kleene tree.

### Syntax and programs

Fix a recursive list \(\theta_0,\theta_1,\ldots\), without repetitions, of
all closed arithmetic formulas written using atomic formulas, negation,
conjunction and existential quantification. Other connectives are effective
abbreviations. Such a list is obtained by listing finite strings in length
and lexicographic order and retaining exactly the closed well-formed formulas.
Its inverse is computable on closed formulas by searching the list.

In this section take \(A(m)=1\) exactly when \(\theta_m\) is true. This
oracle is computably equivalent to the one used in Lemma 1. Fix a standard
effective enumeration \((\Phi_e^X)\) of oracle programs with natural number
inputs and outputs, and a step-by-step universal simulation. The enumeration
contains every partial function computable from \(X\).

### Finite records and the membership test

A node of length \(N\) is a list
\[
 s=\bigl((b_0,w_0,d_0),\ldots,(b_{N-1},w_{N-1},d_{N-1})\bigr),
 \tag{6}
\]
where each \(b_m\in\{0,1\}\) and each \(w_m,d_m\in\mathbb N\).
Think of \(b\) as a proposed truth table, \(w\) as proposed existential
witnesses and \(d\) as diagonal values. Reject a decoded record immediately
if any \(b_m\notin\{0,1\}\). Otherwise accept the node exactly when all the
following finite tests pass.

For each \(m<N\):

1. If \(\theta_m\) is atomic, require that \(b_m\) is its actual, directly
   computable truth value in \(\mathbb N\).
2. If \(\theta_m=\neg\theta_r\) and \(r<N\), require
   \(b_m=1-b_r\).
3. If \(\theta_m=\theta_r\wedge\theta_t\) and \(r,t<N\), require
   \(b_m=b_rb_t\).
4. If \(\theta_m=\exists v\,\psi(v)\):
   - when \(b_m=1\), compute the index \(r\) of
     \(\psi(\bar w_m)\); if \(r<N\), require \(b_r=1\);
   - when \(b_m=0\), for every \(k<N\), compute the index \(r\) of
     \(\psi(\bar k)\); if \(r<N\), require \(b_r=0\).

In addition, for each \(e<N\), simulate \(\Phi_e^b(e)\) for at most
\(N\) steps using the finite table \(b_0,\ldots,b_{N-1}\). If the program
asks an oracle question numbered \(q\geq N\), **defer that simulation**;
do not answer the question with a guessed zero. If it halts within the
allowed simulation, with all queries answered by the available table, and
has output \(y\), require
\[
 d_e\ne y.
 \tag{7}
\]

Call the accepted nodes \(P\). This membership algorithm is total and uses
no oracle. Inverse syntax searches in test 4 terminate because their inputs
are closed formulas in the list. There is no assertion that this algorithm
is fast.

**Lemma 2.** The set \(P\) is a recursive tree, has an infinite branch, and
has no infinite branch computable from \(A\).

**Proof.** All checks are finite and decidable. If a prefix fails a check,
every extension fails the same check: the relevant entries are unchanged,
and simulation time and available oracle answers only increase. Hence \(P\)
is closed under taking prefixes.

For existence of a branch, set \(b_m=A(m)\). When \(\theta_m\) is a true
existential sentence, let \(w_m\) be its least true witness; set \(w_m=0\)
otherwise. Define
\[
 d_e=\begin{cases}
 \Phi_e^A(e)+1,&\text{if }\Phi_e^A(e)\text{ halts},\\
 0,&\text{otherwise}.
 \end{cases}
 \tag{8}
\]
The prefixes of this sequence pass every test, so it is a branch. This
argument uses actual truth to prove existence of the branch, not to test
membership of finite nodes. In fact the particular branch just described
is computable from \(A'\).

Conversely, let \((b,w,d)\) be any branch. The finite checks eventually
apply to every particular subformula index and every particular witness.
Induction on the number of logical connectives and quantifiers in a formula
shows that \(b_m=A(m)\) for all \(m\). Substituting a numeral can lengthen a
term, but does not add logical connectives or quantifiers. In the existential
step, a proposed true existential has its
selected true instance; a proposed false existential has all its instances
false. These are both needed: one-sided witness checks would allow false
truth tables.

If this branch were \(A\)-computable, then \(e\mapsto d_e\) would be a
total \(A\)-computable function, so \(d=\Phi_q^A\) for some \(q\).
The computation \(\Phi_q^A(q)\) has finite running time and asks only
finitely many oracle questions. At a sufficiently long prefix, its entire
computation is available to test (7). That test would require
\(d_q\ne\Phi_q^A(q)=d_q\), a contradiction. \(\square\)

The witness coordinates are unbounded natural numbers. The tree is not
claimed computably bounded or finitely branching. In particular, finite
search does not certify which nodes have infinite continuations.

## 4. The specified order on natural numbers

To make the domain literally \(\mathbb N\), use Cantor pairing
\[
 \langle a,b\rangle=(a+b)(a+b+1)/2+b.
\]
Encode a triple by \(\langle b,\langle w,d\rangle\rangle\). Encode a finite
list recursively by
\[
 \operatorname{code}([\,])=0,\qquad
 \operatorname{code}(h::s)=1+\langle h,\operatorname{code}(s)\rangle.
 \tag{9}
\]
Here \(h::s\) is the list with head \(h\) and tail \(s\). This is a
computable bijection between finite lists of natural numbers
and natural numbers: decoding the tail strictly decreases the code.

Decode every \(i\in\mathbb N\) as a finite list of triples. Put
\[
 j\prec_* i\quad\Longleftrightarrow\quad
 i,j\text{ decode to nodes of }P\text{ and the node }j
 \text{ properly extends the node }i.
 \tag{10}
\]
Numbers whose decoded records fail the test for \(P\) are isolated vertices.

**Lemma 3.** Relation (10) is a recursive strict partial order on
\(\mathbb N\). It is ill-founded and has no \(A\)-computable infinite
descending sequence.

**Proof.** Membership in \(P\) and proper extension of finite lists are
decidable. Proper extension is irreflexive and transitive, giving the strict
partial order. The successive prefixes of the branch in Lemma 2 give an
infinite descending sequence, with this orientation of \(\prec_*\).

From any \(A\)-computable infinite descending sequence we could compute an
\(A\)-computable branch through \(P\). To obtain its \(m\)-th record,
search along the sequence for a node of length greater than \(m\) and
read that record. Lengths strictly increase, so the search halts; all these
nodes extend one another. If the sequence starts above the empty node,
its first node simply supplies the missing initial records. This contradicts
Lemma 2. \(\square\)

## 5. The witnessing hierarchy and its effective index

**Theorem 4.** Order \(\prec_*\) in (10) witnesses Alexander's Theorem
79(1). More specifically, for each closed-r.e.-generic \(B\), the family
constructed in Lemma 1 is uniformly r.e. and true. Every \(T_i\) contains
the particular-code schemas (1) for every \(j\), including \(j=i\), and
contains all truth schemas for \(j\prec_* i\).

**Proof.** Apply Lemma 1 to Lemma 3. Once the family is true, all its
consequences are true in the same canonical model, by the meaning of
semantic consequence. \(\square\)

For a single concrete choice of background, take \(B_i\) to consist of the
Peano axioms for the full modal language \(L\), uniformly in \(i\).
Alexander's Lemmas 10 and 20 establish genericity. Thus all the machines
know this arithmetic, have the required particular codes of all machines,
and know their subordinates' truthfulness.

For clarity, invoking the effective recursion theorem here does not leave
an uncomputable choice of a successful index. An explicit standard
compiler is as follows. Given the total computable index transformation
\(f\) in (2), let \(d(x)\) be the effectively compiled index of the
enumerator which first computes the ordinary program output
\(\varphi_x(x)\), then enumerates \(W_{\varphi_x(x)}\). Let \(a\) be the
effectively obtained program index for the total function
\(x\mapsto f(d(x))\), and output \(n=d(a)\). Then
\[
 W_n=W_{\varphi_a(a)}=W_{f(d(a))}=W_{f(n)}.
 \tag{11}
\]
The compiler uses the usual parameter theorem and a fixed acceptable
numbering; it never tests whether a theory is true. The numerical value of
\(n\) depends on the chosen programming language, syntax coding and
published consequence enumerator. Equations (1), (2), (9), (10), (11) and
the finite membership test specify the hierarchy algorithmically without
searching for an order to which an existence theorem happens to apply.

## 6. Why this coexists with the negative 3.2.1 result

The indices along an actual descending path in this order cannot be
generated by an ordinary algorithm; they cannot even be generated with
arithmetic truth as an oracle. Consequently relabelling those members
\(K_0,K_1,\ldots\) along the path is not a recursive renaming of the modal
language. The tree, order and family enumerator are nevertheless ordinary
computable or r.e. objects.

No arithmetic truth predicate has been added to the machines' language or
assumed to be known by them. Arithmetic truth is used externally in the
soundness proof. The finite order test handles only candidate tables and
finite simulations. Similarly, a known code of a subordinate does not
provide a method for selecting an infinite continuation through the tree.

The construction excludes no requirement of the literal statement of
Theorem 79(1): it retains uniform r.e. access, standard canonical semantics,
all-formula subordinate truth, particular codes of everyone, and full
modal-language arithmetic when that background is selected. It is not
claimed to instantiate the different stratified construction in part (2).

## 7. Relation to paper 07

[Paper 07](../../07-minimal-introspection-bundle/minimal-introspection-bundle.md),
*Minimal building blocks for introspection in self-referential theories*,
concerns the background \(B\), not the order \(\prec_*\). Its positive
result says that the bundle
\[
 [\operatorname{AV}]_i\;\cup\;
 [i\text{-Deduction}]_i\;\cup\;
 [i\text{-Introspection}]_j
 \tag{12}
\]
is closed-r.e.-generic, without also including \(i\)-Validity among the
three candidate supporting schemas. Its minimality claim is restricted
to that named pool of schemas.

One can enrich the concrete background above by the uniform union of
(12) over all \(i,j\). The union is r.e.; unions of such generic families
are generic by Alexander's Lemma 15. The same fixed-point compiler and
soundness proof therefore work with that enriched background. This gives
the requested connection: paper 07 provides an optional smaller supporting
bundle for introspection inside an explicit ill-founded example. It is not
needed for the basic witness, which already works with the published PA
background alone. No claim about minimal background assumptions of the
witness follows from paper 07's restricted minimality result.

## 8. Proof review and boundaries

The potentially delicate points were checked within this main-thread
derivation:

- Canonical truth is reducible to arithmetic truth for each individual
  formula, uniformly from a uniformly r.e. family, using Alexander's actual
  consequence relation and the translation in his proof of Theorem 79.
- Unsound indices need only be enumerated relative to truth. Deciding
  global soundness, which could require a stronger oracle, is unnecessary.
- Closure-generated axioms are true in the canonical model without an
  induction hypothesis. Subordinate truth is the only generator requiring
  the downward argument.
- The finite tree checks both positive existential witnesses and every
  eventually available negative instance. Unsupported positive witnesses
  or one-sided negative checks would invalidate the construction.
- Oracle simulations are deferred on unavailable queries. Guessing answers
  would destroy the diagonal argument and prefix-closure justification.
- Diagonalization concerns all oracle programs and all eventual finite
  halting computations. Testing only a fixed finite selection would not
  establish the absence of an oracle-computable branch.
- The infinitely branching tree and the ordinary computability of its
  membership test are compatible with the use of arithmetic truth in the
  external existence proof. A computable infinite path is not produced.
- Fixed-point compilation is effective. No application of Theorem 79's
  nonconstructive selection of an order remains in the construction.

These are hand checks, not independent review. No finite experiment could
establish the claimed infinite-path property. A complete executable modal
theory enumerator or a formal proof assistant development has not been
produced here.

## Sources

Samuel Allen Alexander, *Self-referential theories*, Journal of Symbolic
Logic **85**(4) (2020), 1687–1716,
[arXiv:2008.11535v1](https://arxiv.org/abs/2008.11535v1),
[full text](https://arxiv.org/html/2008.11535v1),
[DOI](https://doi.org/10.1017/jsl.2020.54).
The relevant dependencies are Definitions 7 and 12–14; Theorem 3; Lemmas 8,
10, 15 and 20; the fixed-point construction and local induction step of
Theorem 24; and the arithmetic translation in the proof of Theorem 79.
The relative diagonal argument, finite syntax checks and effective recursion
theorem are standard computability methods; their use here is written out.
