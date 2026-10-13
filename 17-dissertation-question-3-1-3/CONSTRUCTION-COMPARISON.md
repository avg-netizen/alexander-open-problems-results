# Historical comparison of the auxiliary constructions

This note preserves the comparison and source-correspondence discussion from
the [8 October edition](archive/2026-10-08/README.md). It records that edition's
claims and terminology. The [current standalone paper](README.md) states its
mathematical construction without requiring this history; the
[Lean comparison](../alexander-dissertation-lean/paper/LEAN-COMPARISON-2026-10-13.md)
owns the formal verification scope. The section numbers below are those of the
archived edition.

### 18.3. The specified larger core is strictly stronger

To compare the cores in the same language, write \(U^-=U\), and define
\[
U^+=\operatorname{cl}_*\left(
 B_*+\{\operatorname{MC}_b(\varphi;x):b\in I,\ \varphi,\ x\}
\right).
\tag{P3}
\]
This is the code-free auxiliary theory of the earlier prose approach. It adds the core's own mechanicalness instances to the displayed generator table.

The inclusion \(U^-\subseteq U^+\) is immediate, but strictness requires proof.

**Strictness proposition.** In the enlarged base logic,
\[
\operatorname{Th}(U^-)\subsetneq\operatorname{Th}(U^+).
\]

**Proof.** Define an arithmetic translation \(E\) by
\[
E(K_*\psi)=E(\psi),\qquad
E(K_j\psi)=\bot\quad(j\in\mathbb N),
\]
and let it commute with arithmetic symbols, Boolean operations, and quantifiers. Interpret formulas over standard \(\mathbb N\) by
\[
M_E\models\varphi[s]\quad\Longleftrightarrow\quad
\mathbb N\models E(\varphi)[s].
\]
The translation respects alphabetic changes and capture-free substitution, and its truth depends only on free variables. Thus this is an admissible base-logical structure with the numerical-assignment property.

All \(B_*\)-generators are true. Modal induction is induction on a subset of standard \(\mathbb N\). Core validity, deduction, introspection, and core reflection become their transparent classical counterparts. Original-owner reflection has a false antecedent. Actual validity and Assigned Validity hold as in Section 2.

Every original knowledge column is empty, so a fixed empty-program index witnesses every original-owner mechanicalness generator, including its parameter version. A core prefix preserves truth because \(K_*\) is transparent in this model. Hence \(M_E\models U^-\).

Let
\[
\chi(x)=\neg W(x,x).
\]
Its arithmetic truth set is the diagonal nonhalting set
\[
D=\{n:n\notin W_n\}.
\]
This set is not r.e.: if \(D=W_d\), then \(d\in W_d\) would be equivalent to \(d\notin W_d\). In \(M_E\), the column for \(K_*\chi(x)\) is exactly \(D\). Therefore
\[
\operatorname{MC}_*(\chi;x)=
\exists e\,\forall x
 \bigl(K_*\chi(x)\leftrightarrow W(e,x)\bigr)
\tag{P4}
\]
is false in \(M_E\).

By base-logical soundness, \(U^-\) does not prove (P4). The theory \(U^+\) contains it as a generator. This proves strict inclusion. \(\square\)

The separating structure is a base-logical countermodel, not a claim that its transparent core is itself an r.e. knowing machine. Arbitrary admissible structures are the correct models for this nonprovability argument.

There is also an exact statement about the intended source model of the revised proof. Since \(U^-\) is r.e., its own actual \(\chi\)-knowledge column is r.e., so (P4) is externally true there. But \(U^-\) does not prove (P4), so the actual \(U^-\) core does not know this instance of its own mechanicalness. The earlier prescribed core would know it.

This comparison concerns the specified core theories. It does not prove
\(\operatorname{Th}(T_i^-)\subseteq\operatorname{Th}(T_i^+)\) for the resulting original-agent constructions. Changing the core changes the literal code numerals and the recursion fixed point, so their original generator sets are not simply nested.

### 18.4. A self-mechanical common agent already follows from 3-1-3

Given \(R\), add a new least agent \(*\), with
\[
*\,R^*\,i\quad\text{for every original }i,
\]
retain all original edges, and put no edges below \(*\). The relation \(R^*\) is r.e. and well founded. Code its countable owner set effectively by \(\mathbb N\).

Applying the theorem to \(R^*\) produces a distinguished agent \(*\) that knows everyone's truthfulness and mechanicalness, including its own, and whose particular unary codes are known by every original agent. Thus the existence of such an additional common agent is already a consequence of unrestricted 3-1-3.

Even a fixed, \(R\)-independent theory for such an agent is available from the revised construction. Apply it to \(R^*\), using a second temporary auxiliary owner \(\dagger\). The desired \(*\) is now an original owner relative to \(\dagger\), so \(U_\dagger\) includes mechanicalness for \(*\).

Choose \(U_\dagger\) and its compiler \(d_\dagger\) once, independently of \(R\), as in Section 3.2. The least original agent has no subordinate-code generators. Its enlarged theory is therefore the fixed theory
\[
V_*=
\operatorname{cl}_*\left(
 B_*+
 \left\{\forall x\bigl(
 K_\dagger\varphi\leftrightarrow
 W(\overline{d_\dagger(\varphi)},x)\bigr):
                       \operatorname{FV}(\varphi)=\{x\}\right\}
\right).
\tag{P5}
\]
It inherits \(U_\dagger\), including mechanicalness for \(*\). All other original agents know its particular codes along their added edges. Removing \(\dagger\) by Section 17.5 gives a fixed distinguished theory \(V'\) in the desired language.

In fact,
\[
\operatorname{Th}(U^+)\subseteq\operatorname{Th}(V').
\tag{P5a}
\]
The reduct \(V'\) contains every \(B_*\)-generator, inherits mechanicalness for every remaining owner from \(U_\dagger\), and is closed under own sentence necessity. It therefore contains every finite \(*\)-prefix of every generator of \(U^+\), and consequence closure gives (P5a).

The constructed standard knowing-machine model interprets \(K_*\) by \(V'\)-theoremhood and makes every \(V'\)-theorem true. It consequently satisfies every axiom of \(U^+\). Thus the finite-guard revision already proves ordinary consistency of \(U^+\), and more specifically gives a standard knowing-machine model of its axiom set.

This does not identify \(V'\) with the exact code-free \(U^+\), or show that the same result holds after replacing the raw \(*\)-predicate by exact \(U^+\)-theoremhood. In particular, it does not establish the earlier genericity theorem for that exact predicate. Formulas can contain negative occurrences of knowledge, so changing the theory changes their interpretation; subtheory inclusion alone does not justify the replacement.

### 18.5. Which proof is more general?

There are different directions of strength.

| Feature | Finite-guard revision | Earlier larger-core approach |
|---|---|---|
| Original 3-1-3 target | All three unrestricted schemas | The same target |
| Primitive auxiliary mechanicalness | Original owners only | Includes the auxiliary core itself |
| Auxiliary genericity | Proved here for the exact \(U^-\) and column-admissible outside predicates | Seeks genericity for the specified \(U^+\) |
| Ordinal input for the extension argument | Arbitrarily large finite guards and finite rooms in the complete core | The stronger ordinal apparatus supporting a global cofinal coherent chain |
| Recovery statement needed for soundness | A selected finite room table for each target, uniformly across its numerical instances | Recovery for arbitrary suitable source-shared lifts on the chosen global chain |
| Fixed self-mechanical common agent | Obtainable by the additional-agent construction above | Supplied directly by the prescribed larger core, if its stronger theorem is established |

The revised extension proof has weaker ordinal hypotheses, and its column-admissible formulation covers a wider class of temporary semantic predicates than a jointly r.e. formulation. The earlier core assertion has a stronger specified conclusion about \(U^+\). The earlier global lifting statement uses a chain that the complete-core input here does not provide. Neither entire argument is uniformly “more general” in every respect.

For this theorem, the selected-room quantifier order is enough:
\[
\forall\theta\ \exists\mathscr R_\theta\;
\forall\psi\ \forall s\ \forall\pi\;
\exists\mathscr D_{\theta,\psi,s,\pi}.
\tag{P6}
\]
Here \(\mathscr R_\theta\) is one finite target room and its label table; \(\psi\) ranges over the target and the formulas in its finitely many required query-shape classes, including all term variants; \(s\) is a numerical assignment; \(\pi\) is a finite source certificate for the required instance; and \(\mathscr D\) is the additional finite proof room and reflection data. The target table is fixed before every such variant and instance. The additional proof room may depend on the certificate.

For the extension stages considered here, the fixed-label lemma also recovers the corresponding global-chain lifting corollary if a suitable cofinal pairwise-\(\leq_2\) chain is supplied as an additional ordinal assumption. A finite prescribed chain-supported lift has a later chain point above its support; the subsequent chain points provide a guard of any required finite rank there. Lemma 14 proves recovery below that point, and erasure gives the reverse implication. Thus the finite-guard transport method does not preclude the stronger-input corollary. This proof uses the smaller ordinal input and the per-target room statement. The separate assertion about exact \(U^+\)-core genericity still requires its own argument.

### 18.6. No higher affirmative matrix cell follows

In Alexander's matrix, the first and third coordinates of 3-1-3 are already maximal: everyone knows everyone's truthfulness and everyone's mechanicalness. Increasing the middle coordinate to 2 requires the full known-particular-self-code schema while retaining known self-truthfulness. Reinhardt's negative theorem excludes this under the relevant Epistemic Arithmetic assumptions [A, §1.1, pp. 1–2, 5, and 7]. In particular, the stronger ordinal apparatus cannot turn 3-2-3 or 3-3-3 into affirmative results.

This concerns the entire self-code schema. An agent may know a particular code for an individual trivial column without contradiction.

The additional content worth distinguishing is therefore the exact auxiliary theory and its extension property, the uniform parameter schemas, and the scope of the lifting theorem. The finite-guard revision establishes the original 3-1-3 target together with Sections 18.1–18.2 and the additional-agent constructions above.

## References and source correspondence

**[A]** Samuel A. Alexander, *The Theory of Several Knowing Machines*, doctoral dissertation, The Ohio State University, 2013. The supplied PDF is the source used here. Relevant locations: §1.1 and Definition 1.1.1 for the matrix and negative boundary; §1.2, Definitions 1.2.3, 1.2.9, 1.2.15, 1.2.17, and 1.2.19, Theorem 1.2.6, and Example 1.2.13 for the logic and machine semantics; §2.6, p. 75, for inheritance along transitive closure. [Official dissertation record](https://etd.ohiolink.edu/acprod/odb_etd/etd/r/1501/10?clear=10&p10_accession_num=osu1366362999).

**[W17]** Gunnar Wilken, *Tracking chains revisited*, 2017 version. §5.1 and Corollary 5.8 give the elementary-recursive characterization used for the core. [Primary text](https://arxiv.org/html/1611.04348v3).

**[W18]** Gunnar Wilken, *Pure patterns of order 2*, 2018 version. Corollaries 4.8 and 4.10 give the finite-pattern realization and core results used in the finite-tallness argument. [Primary text](https://arxiv.org/html/1608.08421v5).

**[W21]** Gunnar Wilken, *Pure \(\Sigma_2\)-Elementarity beyond the Core*, 2021 version. The supplied PDF is the source used here. Printed pp. 5–6 include the pure relations, Lemma 1.7, the core identification, and Theorem 1.8. Theorem 4.2 and Corollary 4.6 supply the corrected semantic characterization. [Preprint record](https://arxiv.org/abs/1710.01870).

The supplied handoff's recorded-stage development is the source of the finite-guard architecture expanded here. Its corresponding components are `RecordedBackground`, `RecordedMain`, `FullRecordedAdmissions`, `FullRecordedPrefixes`, `RecordedStageContexts`, `RecordedFixedLabelTransport`, `StageMainRow`, `StageCutSoundness`, and `IdealGenericityInduction`, together with the source-family and column-genericity modules. The arguments above state and prove their mathematical content; source names are correspondence aids, not additional mathematical hypotheses.
