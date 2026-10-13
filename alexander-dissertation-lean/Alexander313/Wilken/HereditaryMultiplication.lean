import Alexander313.Wilken.HereditaryCanonicalCoefficients
import Alexander313.Wilken.HereditaryLogEnd
import Alexander313.Wilken.MultiplicativePrincipalArithmetic

/-!
# Actual multiplication on the original hereditary union

The executing search checks a finite certificate containing the real leading
omega exponent of the left input and a real exponent for every canonical right
coefficient head. These are the existing primitive recursive principal-log
graphs, not supplied arithmetic or logarithm predicates. A primitive recursive
fold uses actual canonical sums, omega powers and right finite products.
Finitely many proved principal-log witnesses derive search termination on
exactly pairs of originally admitted inputs. The resulting multiplication is
partial recursive; its unbounded logarithm search is not claimed PR.

The ordinal proof uses the genuine leading-head multiplication law and right
distributivity. Canonical admission and value injection give a unique actual
output and representation invariance. All proof terms remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Multiplication

abbrev Entry := (Nat × Nat) × Nat

def decodeEntries (c : Nat) : List Entry :=
  (Encodable.decode (α := List Entry) c).getD []

theorem decodeEntries_primrec : Primrec decodeEntries :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

@[simp] theorem decodeEntries_encode (es : List Entry) :
    decodeEntries (Encodable.encode es) = es := by
  simp [decodeEntries, Encodable.encodek]

def entryRuns (es : List Entry) : CanonicalCoefficients.Form := es.map Prod.fst

theorem entryRuns_primrec : Primrec entryRuns :=
  Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd).to₂

def entriesCheck : List Entry → Bool
  | [] => true
  | e :: es => PrincipalLogarithm.graph e.1.1 e.2 && entriesCheck es

theorem entriesCheck_primrec : Primrec entriesCheck := by
  have hs : Primrec₂ (fun (_ : List Entry) (p : Entry × Bool) =>
      PrincipalLogarithm.graph p.1.1.1 p.1.2 && p.2) :=
    (Primrec.and.comp
      (PrincipalLogarithm.graph_primrec.comp
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.id (Primrec.const true) hs
  have he : (fun es : List Entry => es.foldr
      (fun e b => PrincipalLogarithm.graph e.1.1 e.2 && b) true) = entriesCheck := by
    funext es
    induction es with
    | nil => rfl
    | cons e es ih => simp only [List.foldr_cons, entriesCheck, ih]
  exact h.of_eq (fun p => congrFun he p)

theorem entriesCheck_exact (es : List Entry) : entriesCheck es = true ↔
    ∀ e ∈ es, PrincipalLogarithm.graph e.1.1 e.2 = true := by
  induction es with
  | nil => simp [entriesCheck]
  | cons e es ih => simp only [entriesCheck, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem entries_witness (rs : CanonicalCoefficients.Form)
    (hr : ∀ p ∈ rs, Principal.unionPrincipalCheck p.1 = true) :
    ∃ es : List Entry, entryRuns es = rs ∧ entriesCheck es = true := by
  revert hr
  induction rs with
  | nil => intro _; exact ⟨[], rfl, rfl⟩
  | cons p rs ih =>
    intro hr
    obtain ⟨d, hd⟩ := PrincipalLogarithm.graph_witness p.1 (hr p List.mem_cons_self)
    obtain ⟨es, he, hs⟩ := ih (fun s hs => hr s (List.mem_cons_of_mem _ hs))
    exact ⟨(p, d) :: es, by simp only [entryRuns, List.map_cons] at he ⊢; rw [he],
      by simp only [entriesCheck, hd, hs, Bool.true_and]⟩

def zeroCode : Nat := Canonical.canonicalize Alexander313.HereditaryOrdinalLabels.zeroCode

theorem zeroCode_checked : Canonical.check zeroCode = true :=
  Canonical.canonicalize_check _ Alexander313.HereditaryOrdinalLabels.zeroCode_checked

theorem zeroCode_value : unionInterpretation zeroCode = 0 :=
  (Canonical.canonicalize_value _ Alexander313.HereditaryOrdinalLabels.zeroCode_checked).trans
    Alexander313.HereditaryOrdinalLabels.zeroCode_value

/-- A zero head exponent means the right principal is exactly one. -/
def factor (q : Nat) (g d : Nat) : Nat :=
  cond (OmegaPowers.zeroCheck d) (Canonical.canonicalize q)
    (OmegaPowers.powerCode (CanonicalArithmetic.canonicalSum g d))

theorem factor_primrec : Primrec (fun p : Nat × (Nat × Nat) => factor p.1 p.2.1 p.2.2) :=
  Primrec.cond
    (OmegaPowers.zeroCheck_primrec.comp (Primrec.snd.comp Primrec.snd))
    (Canonical.Effective.canonicalize_primrec.comp Primrec.fst)
    (OmegaPowers.powerCode_primrec.comp
      (CanonicalArithmetic.canonicalSum_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)))

theorem factor_checked (q g d : Nat) (hq : unionCheck q = true)
    (hg : Canonical.check g = true) (hd : Canonical.check d = true) :
    Canonical.check (factor q g d) = true := by
  cases hz : OmegaPowers.zeroCheck d with
  | false =>
    simp only [factor, hz, Bool.cond_false]
    exact OmegaPowers.powerCode_checked _ (CanonicalArithmetic.canonicalSum_original _ _
      (Canonical.check_original hg) (Canonical.check_original hd))
  | true =>
    simp only [factor, hz, Bool.cond_true]
    exact Canonical.canonicalize_check q hq

def term (q g : Nat) (e : Entry) : Nat :=
  FiniteMultiplication.multiplyCode (factor q g e.2) e.1.2

theorem term_primrec : Primrec (fun p : (Nat × Nat) × Entry => term p.1.1 p.1.2 p.2) :=
  FiniteMultiplication.multiplyCode_primrec.comp
    (factor_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd))))
    (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))

def fold (q g : Nat) : List Entry → Nat
  | [] => zeroCode
  | e :: es => CanonicalArithmetic.canonicalSum (term q g e) (fold q g es)

theorem fold_primrec : Primrec (fun p : (Nat × Nat) × List Entry => fold p.1.1 p.1.2 p.2) := by
  have hs : Primrec₂ (fun (p : (Nat × Nat) × List Entry) (s : Entry × Nat) =>
      CanonicalArithmetic.canonicalSum (term p.1.1 p.1.2 s.1) s.2) :=
    (CanonicalArithmetic.canonicalSum_primrec.comp
      (term_primrec.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const zeroCode) hs
  have he : (fun p : (Nat × Nat) × List Entry => p.2.foldr
      (fun e c => CanonicalArithmetic.canonicalSum (term p.1.1 p.1.2 e) c) zeroCode) =
      (fun p => fold p.1.1 p.1.2 p.2) := by
    funext p
    rcases p with ⟨⟨q, g⟩, es⟩
    induction es with
    | nil => rfl
    | cons e es ih => simp only [List.foldr_cons, fold, ih]
  exact h.of_eq (fun p => congrFun he p)

/-- Only finite numerical data and actual existing PR graphs are checked. -/
def certificateCheck (input witness : Nat) : Bool :=
  let q := input.unpair.1
  let v := input.unpair.2
  let g := witness.unpair.1
  let es := decodeEntries witness.unpair.2
  (unionCheck q && unionCheck v) &&
    cond (OmegaPowers.zeroCheck q) true
      ((PrincipalLogarithm.graph (LogEnd.mcCode q) g && entriesCheck es) &&
        (Encodable.encode (entryRuns es) == CanonicalCoefficients.encodeForm v))

theorem certificateCheck_primrec : Primrec₂ certificateCheck := by
  have hi : Primrec (fun p : Nat × Nat => p.1.unpair) := Primrec.unpair.comp Primrec.fst
  have hq := Primrec.fst.comp hi
  have hv := Primrec.snd.comp hi
  have hw : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hg := Primrec.fst.comp hw
  have hes := decodeEntries_primrec.comp (Primrec.snd.comp hw)
  exact (Primrec.and.comp
    (Primrec.and.comp (Uniform.unionCheck_primrec.comp hq) (Uniform.unionCheck_primrec.comp hv))
    (Primrec.cond (OmegaPowers.zeroCheck_primrec.comp hq) (Primrec.const true)
      (Primrec.and.comp
        (Primrec.and.comp (PrincipalLogarithm.graph_primrec.comp (LogEnd.mcCode_primrec.comp hq) hg)
          (entriesCheck_primrec.comp hes))
        (Primrec.beq.comp (Primrec.encode.comp (entryRuns_primrec.comp hes))
          (CanonicalCoefficients.encodeForm_primrec.comp hv))))).to₂

def candidate (input witness : Nat) : Nat :=
  cond (OmegaPowers.zeroCheck input.unpair.1) zeroCode
    (fold input.unpair.1 witness.unpair.1 (decodeEntries witness.unpair.2))

theorem candidate_primrec : Primrec₂ candidate := by
  have hq : Primrec (fun p : Nat × Nat => p.1.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hw : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  exact (Primrec.cond (OmegaPowers.zeroCheck_primrec.comp hq) (Primrec.const zeroCode)
    (fold_primrec.comp ((hq.pair (Primrec.fst.comp hw)).pair
      (decodeEntries_primrec.comp (Primrec.snd.comp hw))))).to₂

def certificateSearch (input : Nat) : Part Nat :=
  Nat.rfind (fun witness => Part.some (certificateCheck input witness))

theorem certificateSearch_partrec : Partrec certificateSearch :=
  Partrec.rfind certificateCheck_primrec.to_comp.partrec.to₂

theorem certificateSearch_domain (input : Nat) : (certificateSearch input).Dom ↔
    ∃ witness, certificateCheck input witness = true := by
  simp [certificateSearch, Nat.rfind_dom]

theorem certificateSearch_checked (input witness : Nat) (hw : witness ∈ certificateSearch input) :
    certificateCheck input witness = true := by
  have hs : true ∈ Part.some (certificateCheck input witness) := Nat.rfind_spec hw
  simpa only [Part.mem_some_iff, eq_comm] using hs

def evaluation (input : Nat) : Part Nat :=
  (certificateSearch input).bind (fun witness => Part.some (candidate input witness))

theorem evaluation_partrec : Partrec evaluation :=
  certificateSearch_partrec.bind candidate_primrec.to_comp.partrec.to₂

def multiply (q v : Nat) : Part Nat := evaluation (Nat.pair q v)

theorem multiply_partrec : Partrec₂ multiply :=
  (evaluation_partrec.comp Primrec₂.natPair.to_comp).to₂

theorem certificateCheck_original (input witness : Nat)
    (hw : certificateCheck input witness = true) :
    unionCheck input.unpair.1 = true ∧ unionCheck input.unpair.2 = true :=
  Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1

theorem certificateCheck_nonzero (input witness : Nat)
    (hw : certificateCheck input witness = true) (hz : OmegaPowers.zeroCheck input.unpair.1 = false) :
    PrincipalLogarithm.graph (LogEnd.mcCode input.unpair.1) witness.unpair.1 = true ∧
      entriesCheck (decodeEntries witness.unpair.2) = true ∧
      entryRuns (decodeEntries witness.unpair.2) = CanonicalCoefficients.form input.unpair.2 := by
  have ht := (Bool.and_eq_true_iff.mp hw).2
  simp only [hz, Bool.cond_false, Bool.and_eq_true, beq_iff_eq] at ht
  exact ⟨ht.1.1, ht.1.2, Encodable.encode_injective ht.2⟩

/-- Witnesses are obtained separately for each actual principal in the finite
right coefficient list; the executing search itself only handles Nat data. -/
theorem certificateCheck_witness (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    ∃ witness, certificateCheck (Nat.pair q v) witness = true := by
  cases hz : OmegaPowers.zeroCheck q with
  | true =>
    exact ⟨0, by simp only [certificateCheck, Nat.unpair_pair, hq, hv, hz,
      Bool.true_and, Bool.cond_true]⟩
  | false =>
    have hn : unionInterpretation q ≠ 0 := by
      intro he
      have ht := (OmegaPowers.zeroCheck_exact q).mpr ⟨hq, he⟩
      rw [hz] at ht
      contradiction
    have hp := LogEnd.componentCode_principal false q hq hn
    obtain ⟨g, hg⟩ := PrincipalLogarithm.graph_witness (LogEnd.mcCode q)
      ((Principal.unionPrincipalCheck_exact _).mpr
        ⟨Canonical.check_original hp.1, hp.2.1, hp.2.2⟩)
    obtain ⟨es, he, hs⟩ := entries_witness (CanonicalCoefficients.form v) (by
      intro p hp
      have ht := CanonicalCoefficients.form_head_spec v hv p hp
      exact (Principal.unionPrincipalCheck_exact p.1).mpr
        ⟨Canonical.check_original ht.1, ht.2.1, ht.2.2⟩)
    refine ⟨Nat.pair g (Encodable.encode es), ?_⟩
    simp only [certificateCheck, Nat.unpair_pair, hq, hv, hz, Bool.true_and,
      Bool.cond_false, decodeEntries_encode, hg, hs, he, CanonicalCoefficients.encodeForm,
      beq_self_eq_true]

theorem certificateCheck_exists_iff (input : Nat) :
    (∃ witness, certificateCheck input witness = true) ↔
      unionCheck input.unpair.1 = true ∧ unionCheck input.unpair.2 = true := by
  constructor
  · rintro ⟨w, hw⟩
    exact certificateCheck_original input w hw
  · rintro ⟨hq, hv⟩
    have h := certificateCheck_witness input.unpair.1 input.unpair.2 hq hv
    simpa only [Nat.pair_unpair] using h

theorem evaluation_domain (input : Nat) : (evaluation input).Dom ↔
    unionCheck input.unpair.1 = true ∧ unionCheck input.unpair.2 = true := by
  simpa [evaluation, Part.bind_dom, certificateSearch_domain] using certificateCheck_exists_iff input

theorem multiply_domain (q v : Nat) : (multiply q v).Dom ↔
    unionCheck q = true ∧ unionCheck v = true := by
  simpa only [multiply, Nat.unpair_pair] using evaluation_domain (Nat.pair q v)

theorem multiply_terminates (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    (multiply q v).Dom := (multiply_domain q v).mpr ⟨hq, hv⟩

theorem factor_value (q g d : Nat) (hq : unionCheck q = true) (hp : 0 < unionInterpretation q)
    (hg : PrincipalLogarithm.graph (LogEnd.mcCode q) g = true)
    (hd : Canonical.check d = true) :
    unionInterpretation (factor q g d) = unionInterpretation q * Ordinal.omega0 ^ unionInterpretation d := by
  have hgs := (PrincipalLogarithm.graph_exact _ _).mp hg
  cases hz : OmegaPowers.zeroCheck d with
  | true =>
    have hd0 := ((OmegaPowers.zeroCheck_exact d).mp hz).2
    simp only [factor, hz, Bool.cond_true, Canonical.canonicalize_value q hq, hd0,
      Ordinal.opow_zero, mul_one]
  | false =>
    have hdpos : 0 < unionInterpretation d := by
      apply (lt_or_eq_of_le (zero_le)).resolve_right
      intro h0
      have ht := (OmegaPowers.zeroCheck_exact d).mpr ⟨Canonical.check_original hd, h0.symm⟩
      rw [hz] at ht
      contradiction
    obtain ⟨xs, hxs⟩ := LogEnd.mcCode_anf_cons q hq hp
    have hn : IsAdditiveNormalForm (unionInterpretation (LogEnd.mcCode q) :: xs) := by
      rw [← hxs]
      exact canonicalANF_normal _
    have hsum : principalSum (unionInterpretation (LogEnd.mcCode q) :: xs) = unionInterpretation q := by
      rw [← hxs, principalSum_canonicalANF]
    have hm := MultiplicativePrincipalArithmetic.principalSum_mul_omegaPower hn hgs.2.2.2.2.symm hdpos
    rw [hsum] at hm
    rw [factor, hz, Bool.cond_false,
      OmegaPowers.powerCode_value _ (CanonicalArithmetic.canonicalSum_original g d
        (Canonical.check_original hgs.2.2.2.1) (Canonical.check_original hd)),
      CanonicalArithmetic.canonicalSum_value g d
        (Canonical.check_original hgs.2.2.2.1) (Canonical.check_original hd)]
    exact hm.symm

theorem term_checked (q g : Nat) (e : Entry) (hq : unionCheck q = true)
    (hg : Canonical.check g = true) (he : PrincipalLogarithm.graph e.1.1 e.2 = true) :
    Canonical.check (term q g e) = true := by
  have hd := ((PrincipalLogarithm.graph_exact _ _).mp he).2.2.2.1
  exact FiniteMultiplication.multiplyCode_checked _ _
    (Canonical.check_original (factor_checked q g e.2 hq hg hd))

theorem term_value (q g : Nat) (e : Entry) (hq : unionCheck q = true) (hp : 0 < unionInterpretation q)
    (hg : PrincipalLogarithm.graph (LogEnd.mcCode q) g = true)
    (he : PrincipalLogarithm.graph e.1.1 e.2 = true) :
    unionInterpretation (term q g e) = unionInterpretation q *
      (unionInterpretation e.1.1 * (e.1.2 : Ordinal.{0})) := by
  have hgs := (PrincipalLogarithm.graph_exact _ _).mp hg
  have hes := (PrincipalLogarithm.graph_exact _ _).mp he
  rw [term, FiniteMultiplication.multiplyCode_value _ _
    (Canonical.check_original (factor_checked q g e.2 hq hgs.2.2.2.1 hes.2.2.2.1)),
    factor_value q g e.2 hq hp hg hes.2.2.2.1, hes.2.2.2.2, mul_assoc]

theorem fold_checked (q g : Nat) (es : List Entry) (hq : unionCheck q = true)
    (hg : Canonical.check g = true) (he : entriesCheck es = true) :
    Canonical.check (fold q g es) = true := by
  revert he
  induction es with
  | nil => intro _; exact zeroCode_checked
  | cons e es ih =>
    intro he
    have hs := Bool.and_eq_true_iff.mp he
    exact CanonicalArithmetic.canonicalSum_checked _ _
      (Canonical.check_original (term_checked q g e hq hg hs.1))
      (Canonical.check_original (ih hs.2))

theorem fold_value (q g : Nat) (es : List Entry) (hq : unionCheck q = true) (hp : 0 < unionInterpretation q)
    (hg : PrincipalLogarithm.graph (LogEnd.mcCode q) g = true) (he : entriesCheck es = true) :
    unionInterpretation (fold q g es) = unionInterpretation q *
      Coefficients.weightedSum unionInterpretation (entryRuns es) := by
  have hgc := ((PrincipalLogarithm.graph_exact _ _).mp hg).2.2.2.1
  revert he
  induction es with
  | nil => intro _; simp only [fold, zeroCode_value, entryRuns, List.map_nil,
      Coefficients.weightedSum, mul_zero]
  | cons e es ih =>
    intro he
    have hs := Bool.and_eq_true_iff.mp he
    rw [fold, CanonicalArithmetic.canonicalSum_value _ _
      (Canonical.check_original (term_checked q g e hq hgc hs.1))
      (Canonical.check_original (fold_checked q g es hq hgc hs.2)),
      term_value q g e hq hp hg hs.1, ih hs.2]
    simp only [entryRuns, List.map_cons, Coefficients.weightedSum, mul_add]

theorem candidate_value (input witness : Nat) (hw : certificateCheck input witness = true) :
    Canonical.check (candidate input witness) = true ∧
      unionInterpretation (candidate input witness) =
        unionInterpretation input.unpair.1 * unionInterpretation input.unpair.2 := by
  have hd := certificateCheck_original input witness hw
  cases hz : OmegaPowers.zeroCheck input.unpair.1 with
  | true =>
    have h0 := ((OmegaPowers.zeroCheck_exact _).mp hz).2
    simp only [candidate, hz, Bool.cond_true, zeroCode_checked, zeroCode_value, h0, zero_mul,
      and_self]
  | false =>
    have hs := certificateCheck_nonzero input witness hw hz
    have hp : 0 < unionInterpretation input.unpair.1 := by
      apply (lt_or_eq_of_le (zero_le)).resolve_right
      intro h0
      have ht := (OmegaPowers.zeroCheck_exact _).mpr ⟨hd.1, h0.symm⟩
      rw [hz] at ht
      contradiction
    simp only [candidate, hz, Bool.cond_false]
    refine ⟨fold_checked _ _ _ hd.1 ((PrincipalLogarithm.graph_exact _ _).mp hs.1).2.2.2.1 hs.2.1, ?_⟩
    rw [fold_value _ _ _ hd.1 hp hs.1 hs.2.1, hs.2.2,
      CanonicalCoefficients.form_weighted_value _ hd.2]

theorem evaluation_witness (input c : Nat) (hc : c ∈ evaluation input) :
    ∃ witness, certificateCheck input witness = true ∧ candidate input witness = c := by
  obtain ⟨w, hw, he⟩ := Part.mem_bind_iff.mp hc
  refine ⟨w, certificateSearch_checked input w hw, ?_⟩
  simpa only [Part.mem_some_iff, eq_comm] using he

theorem multiply_value (q v c : Nat) (hc : c ∈ multiply q v) :
    unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q * unionInterpretation v := by
  obtain ⟨w, hw, he⟩ := evaluation_witness (Nat.pair q v) c hc
  have hd := certificateCheck_original _ _ hw
  have hs := candidate_value _ _ hw
  rw [he] at hs
  simpa only [Nat.unpair_pair] using And.intro hd.1 (And.intro hd.2 hs)

theorem multiply_original (q v c : Nat) (hc : c ∈ multiply q v) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) := by
  have hs := multiply_value q v c hc
  exact ⟨Canonical.check_original hs.2.2.1, Canonical.check_normal hs.2.2.1⟩

theorem multiply_returns (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    ∃ c, c ∈ multiply q v ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q * unionInterpretation v := by
  have hd := multiply_terminates q v hq hv
  have hm : (multiply q v).get hd ∈ multiply q v := ⟨hd, rfl⟩
  exact ⟨_, hm, (multiply_value q v _ hm).2.2⟩

theorem multiply_output_unique (q v c d : Nat) (hc : c ∈ multiply q v) (hd : d ∈ multiply q v) : c = d := by
  have hcs := multiply_value q v c hc
  have hds := multiply_value q v d hd
  exact Canonical.check_value_injective c d hcs.2.2.1 hds.2.2.1 (hcs.2.2.2.trans hds.2.2.2.symm)

theorem multiply_invariant (q v q' v' c d : Nat) (hc : c ∈ multiply q v) (hd : d ∈ multiply q' v')
    (hq : unionInterpretation q = unionInterpretation q') (hv : unionInterpretation v = unionInterpretation v') : c = d := by
  have hcs := multiply_value q v c hc
  have hds := multiply_value q' v' d hd
  exact Canonical.check_value_injective c d hcs.2.2.1 hds.2.2.1
    (hcs.2.2.2.trans (by rw [hq, hv]; exact hds.2.2.2.symm))

theorem multiply_graph_iff (q v c : Nat) : c ∈ multiply q v ↔
    unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
      unionInterpretation c = unionInterpretation q * unionInterpretation v := by
  constructor
  · exact multiply_value q v c
  · rintro ⟨hq, hv, hc, he⟩
    obtain ⟨d, hd, hdc, hdv⟩ := multiply_returns q v hq hv
    have hcd := Canonical.check_value_injective c d hc hdc (he.trans hdv.symm)
    rw [hcd]
    exact hd

theorem multiply_unique (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    ∃! c, c ∈ multiply q v := by
  obtain ⟨c, hc, _⟩ := multiply_returns q v hq hv
  exact ⟨c, hc, fun d hd => multiply_output_unique q v d c hd hc⟩

/-- A positive graph search checks the same genuine certificate and the
literal computed result; the rightmost query field is the output code. -/
def graphCertificateCheck (query witness : Nat) : Bool :=
  certificateCheck query.unpair.1 witness && (query.unpair.2 == candidate query.unpair.1 witness)

theorem graphCertificateCheck_primrec : Primrec₂ graphCertificateCheck := by
  have hp : Primrec (fun p : Nat × Nat => p.1.unpair) := Primrec.unpair.comp Primrec.fst
  exact (Primrec.and.comp (certificateCheck_primrec.comp (Primrec.fst.comp hp) Primrec.snd)
    (Primrec.beq.comp (Primrec.snd.comp hp)
      (candidate_primrec.comp (Primrec.fst.comp hp) Primrec.snd))).to₂

theorem graphCertificateCheck_exists_iff (q v c : Nat) :
    (∃ witness, graphCertificateCheck (Nat.pair (Nat.pair q v) c) witness = true) ↔
      unionCheck q = true ∧ unionCheck v = true ∧ Canonical.check c = true ∧
        unionInterpretation c = unionInterpretation q * unionInterpretation v := by
  constructor
  · rintro ⟨w, hw⟩
    have hs : certificateCheck (Nat.pair q v) w = true ∧ c = candidate (Nat.pair q v) w := by
      simpa only [graphCertificateCheck, Nat.unpair_pair, Bool.and_eq_true, beq_iff_eq] using hw
    have hd := certificateCheck_original _ _ hs.1
    have hc := candidate_value _ _ hs.1
    rw [← hs.2] at hc
    simpa only [Nat.unpair_pair] using And.intro hd.1 (And.intro hd.2 hc)
  · rintro ⟨hq, hv, hc, he⟩
    obtain ⟨w, hw⟩ := certificateCheck_witness q v hq hv
    have hs := candidate_value _ _ hw
    have hcw : c = candidate (Nat.pair q v) w := Canonical.check_value_injective _ _ hc hs.1
      (he.trans (by simpa only [Nat.unpair_pair] using hs.2.symm))
    exact ⟨w, by simp only [graphCertificateCheck, Nat.unpair_pair, hw, Bool.true_and,
      beq_iff_eq]; exact hcw⟩

theorem product_below_limit (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    unionInterpretation q * unionInterpretation v < finiteBaseLimit := by
  obtain ⟨c, hc, hcc, hcv⟩ := multiply_returns q v hq hv
  exact (Hereditary.lt_finiteBaseLimit_iff_code _).mpr
    ⟨c, Canonical.check_original hcc, hcv⟩

open Alexander313.HereditaryOrdinalLabels

/-- The typed operation uses the returned executing partial computation,
whose domain has already been proved from original admission. -/
def labelMultiply (μ ν : Label) : Label :=
  let hd := multiply_terminates μ.1 ν.1 (Canonical.check_original μ.2) (Canonical.check_original ν.2)
  ⟨(multiply μ.1 ν.1).get hd,
    (multiply_value μ.1 ν.1 _ (show (multiply μ.1 ν.1).get hd ∈ multiply μ.1 ν.1 from ⟨hd, rfl⟩)).2.2.1⟩

theorem labelMultiply_value (μ ν : Label) : value (labelMultiply μ ν) = value μ * value ν := by
  let hd := multiply_terminates μ.1 ν.1 (Canonical.check_original μ.2) (Canonical.check_original ν.2)
  have hm : (multiply μ.1 ν.1).get hd ∈ multiply μ.1 ν.1 := ⟨hd, rfl⟩
  exact (multiply_value μ.1 ν.1 _ hm).2.2.2

theorem labelMultiply_assoc (μ ν ρ : Label) :
    labelMultiply (labelMultiply μ ν) ρ = labelMultiply μ (labelMultiply ν ρ) := by
  apply value_injective
  simp only [labelMultiply_value, mul_assoc]

theorem labelMultiply_add (μ ν ρ : Label) :
    labelMultiply μ (CanonicalArithmetic.labelAdd ν ρ) =
      CanonicalArithmetic.labelAdd (labelMultiply μ ν) (labelMultiply μ ρ) := by
  apply value_injective
  simp only [labelMultiply_value, CanonicalArithmetic.labelAdd_value, mul_add]

theorem labelMultiply_zero (μ : Label) : labelMultiply μ zeroLabel = zeroLabel := by
  apply value_injective
  simp only [labelMultiply_value, zeroLabel_value, mul_zero]

theorem zero_labelMultiply (μ : Label) : labelMultiply zeroLabel μ = zeroLabel := by
  apply value_injective
  simp only [labelMultiply_value, zeroLabel_value, zero_mul]

theorem labelMultiply_one (μ : Label) : labelMultiply μ CanonicalArithmetic.oneLabel = μ := by
  apply value_injective
  simp only [labelMultiply_value, CanonicalArithmetic.oneLabel_value, mul_one]

theorem one_labelMultiply (μ : Label) : labelMultiply CanonicalArithmetic.oneLabel μ = μ := by
  apply value_injective
  simp only [labelMultiply_value, CanonicalArithmetic.oneLabel_value, one_mul]

end Alexander313.Wilken.RelativeTerm.Hereditary.Multiplication
