import Alexander313.Wilken.HereditaryNativeFixedPointSupport
import Alexander313.Wilken.HereditaryNativeDecomposition

/-!
# Executing repaired native fixed-point and strict supremum tests

The original checked weak-normal native argument is split by the actual
cardinal ANF cut. A real native ANF atom is a higher presentation only when
it is a literal theta-m node equal to the WHOLE residual, its actual divided
high part exceeds Delta, and the literal exposed Delta star is below eta.
The original same-level argument and all theta sorts are inherited from
native admission. The zero branch is explicit; the source base-1 exception
is excluded by the proved literal epsilon-base equation, not dropped by
convention. Strict supremum comparison uses the proved actual domination.
No fixed-point, parser, normalization, comparison or effectivity oracle is
supplied. These primitive-recursive proof candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.FixedPoint

def nodeCandidate (q m d e : Nat) : RelativeTerm Nat → Bool
  | .theta k a => (k == m) && (Comparison.equalCode q e (.theta k a : RelativeTerm Nat).code &&
      Comparison.lessCode q d (Decomposition.highCode m a.code))
  | _ => false

private def nodeTag (t : RelativeTerm Nat) : Nat := (t.code - 1).unpair.1
private def nodeIndex (t : RelativeTerm Nat) : Nat := (t.code - 1).unpair.2.unpair.1
private def nodeArgument (t : RelativeTerm Nat) : Nat := (t.code - 1).unpair.2.unpair.2

private theorem nodeTag_primrec : Primrec nodeTag :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.nat_sub.comp code_primrec (Primrec.const 1)))
private theorem nodeIndex_primrec : Primrec nodeIndex :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
    (Primrec.unpair.comp (Primrec.nat_sub.comp code_primrec (Primrec.const 1)))))
private theorem nodeArgument_primrec : Primrec nodeArgument :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
    (Primrec.unpair.comp (Primrec.nat_sub.comp code_primrec (Primrec.const 1)))))

private def candidateNumeric (q m d e : Nat) (s : RelativeTerm Nat) : Bool :=
  cond (nodeTag s == 2) ((nodeIndex s == m) && (Comparison.equalCode q e s.code &&
    Comparison.lessCode q d (Decomposition.highCode m (nodeArgument s)))) false

private theorem candidateNumeric_eq (q m d e : Nat) (s : RelativeTerm Nat) :
    candidateNumeric q m d e s = nodeCandidate q m d e s := by
  cases s <;> simp [candidateNumeric, nodeCandidate, nodeTag, nodeIndex, nodeArgument,
    RelativeTerm.code, Nat.unpair_pair]

theorem nodeCandidate_primrec : Primrec (fun p : Nat × (Nat × (Nat × (Nat × RelativeTerm Nat))) =>
    nodeCandidate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hq : Primrec (fun p : Nat × (Nat × (Nat × (Nat × RelativeTerm Nat))) => p.1) := Primrec.fst
  have hm : Primrec (fun p : Nat × (Nat × (Nat × (Nat × RelativeTerm Nat))) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat × (Nat × (Nat × (Nat × RelativeTerm Nat))) => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have he : Primrec (fun p : Nat × (Nat × (Nat × (Nat × RelativeTerm Nat))) => p.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hs : Primrec (fun p : Nat × (Nat × (Nat × (Nat × RelativeTerm Nat))) => p.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hhigh := Decomposition.highCode_primrec.comp hm (nodeArgument_primrec.comp hs)
  have h := (Primrec.beq.comp (nodeTag_primrec.comp hs) (Primrec.const 2)).cond
    (Primrec.and.comp (Primrec.beq.comp (nodeIndex_primrec.comp hs) hm)
      (Primrec.and.comp (Comparison.equalCode_primrec.comp (hq.pair (he.pair (code_primrec.comp hs))))
        (Comparison.lessCode_primrec.comp (hq.pair (hd.pair hhigh))))) (Primrec.const false)
  change Primrec (fun p : Nat × (Nat × (Nat × (Nat × RelativeTerm Nat))) =>
    candidateNumeric p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) at h
  simpa only [candidateNumeric_eq] using h

def starCode (q m d e : Nat) : Bool := starLess q m (ThetaCourse.rawTree d) (ThetaCourse.rawTree e)

theorem starCode_primrec : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => starCode p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  starLess_primrec.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
    ((ThetaCourse.rawTree_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
      (ThetaCourse.rawTree_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))

def higherCheck (q m d e : Nat) : Bool := starCode q m d e &&
  (Decomposition.word e).any (nodeCandidate q m d e)

theorem higherCheck_primrec : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => higherCheck p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have htest : Primrec₂ (fun p : Nat × (Nat × (Nat × Nat)) =>
      fun s : RelativeTerm Nat => nodeCandidate p.1 p.2.1 p.2.2.1 p.2.2.2 s) :=
    (nodeCandidate_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
          ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd))))).to₂
  have hany := (SourceOne.Comparison.Effective.listAny_primrec _ htest).comp Primrec.id
    (Decomposition.word_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.and.comp starCode_primrec hany

def zeroCheck (e : Nat) : Bool := (Decomposition.word e).length == 0

theorem zeroCheck_primrec : Primrec zeroCheck :=
  Primrec.beq.comp (Primrec.list_length.comp Decomposition.word_primrec) (Primrec.const 0)

theorem zeroCheck_exact (q e : Nat) (he : Decomposition.inputCheck q e = true) :
    zeroCheck e = true ↔ interpretation q e = 0 := by
  have hv : principalSum ((Decomposition.word e).map (denote q)) = interpretation q e := by
    rw [(Decomposition.word_spec q e he).2, principalSum_canonicalANF]
  cases hw : Decomposition.word e with
  | nil =>
    have hz : interpretation q e = 0 := by rw [← hv, hw]; rfl
    simp [zeroCheck, hw, hz]
  | cons a as =>
    have ha := (Decomposition.word_spec q e he).1 a (by rw [hw]; exact List.mem_cons_self)
    have hp : 0 < interpretation q e := by rw [← hv, hw]; exact ha.2.2.1.trans_le le_self_add
    simp [zeroCheck, hw, ne_of_gt hp]

def inputCheck (q m c : Nat) : Bool := Decomposition.inputCheck q c &&
  decide ((ThetaCourse.rawTree c).outerSort ≤ m + 2)

theorem inputCheck_primrec : Primrec (fun p : Nat × (Nat × Nat) => inputCheck p.1 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : Nat × (Nat × Nat) => Decomposition.inputCheck p.1 p.2.2) := Decomposition.inputCheck_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun p : Nat × (Nat × Nat) => (ThetaCourse.rawTree p.2.2).outerSort) :=
    outerSort_primrec.comp (ThetaCourse.rawTree_primrec.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.and.comp hc ((Primrec.nat_le.comp hs
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2))).decide)

theorem inputCheck_exact (q m c : Nat) : inputCheck q m c = true ↔
    checkCode q c = true ∧ Comparison.Normal q (ThetaCourse.rawTree c) ∧
      interpretation q c < omegaSequence (base q) (m + 2) := by
  simp only [inputCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hs⟩
    have ht := Decomposition.input_tree q c hc
    exact ⟨((Decomposition.inputCheck_exact q c).mp hc).1, ht.2,
      (Decomposition.input_value q c hc).trans_lt
        ((denote_lt_iff_outerSort_le q _ ht.1 (m + 2) (by omega)).mpr hs)⟩
  · rintro ⟨hc, hn, hs⟩
    have hd := (Decomposition.inputCheck_exact q c).mpr ⟨hc, hn⟩
    refine ⟨hd, (denote_lt_iff_outerSort_le q _ (Decomposition.input_tree q c hd).1 (m + 2) (by omega)).mp ?_⟩
    exact (Decomposition.input_value q c hd).symm.trans_lt hs

noncomputable def checkedOrdinal (q m c : Nat) (hc : Decomposition.inputCheck q c = true) :
    GlobalNotationOrdinal (base q) (m + 1) :=
  sourceOrdinal q m (ThetaCourse.rawTree c) (Decomposition.input_tree q c hc).1

@[simp] theorem checkedOrdinal_val (q m c : Nat) (hc : Decomposition.inputCheck q c = true) :
    (checkedOrdinal q m c hc).val = interpretation q c := (Decomposition.input_value q c hc).symm

theorem starCode_exact (q m d e : Nat) (hd : Decomposition.inputCheck q d = true)
    (he : Decomposition.inputCheck q e = true) (hepos : 0 < interpretation q e) :
    starCode q m d e = true ↔ globalStar (base q)
      (base_pos q (Bool.and_eq_true_iff.mp (Decomposition.input_tree q d hd).1).1) m
        (checkedOrdinal q m d hd) < interpretation q e := by
  have hdt := Decomposition.input_tree q d hd
  have het := Decomposition.input_tree q e he
  have hpos : 0 < denote q (ThetaCourse.rawTree e) :=
    hepos.trans_eq (Decomposition.input_value q e he)
  simpa only [starCode, checkedOrdinal, ← Decomposition.input_value q e he] using
    starLess_exact q m _ _ hdt.1 het.1 hdt.2 het.2 hpos

theorem nodeCandidate_higher (q m d e : Nat) (hd : Decomposition.inputCheck q d = true)
    (he : Decomposition.inputCheck q e = true) (s : RelativeTerm Nat)
    (hs : s ∈ Decomposition.word e) (hc : nodeCandidate q m d e s = true)
    (hst : starCode q m d e = true) :
    SourceFixedPointLimits.GlobalHigherPresentation (base q)
      (base_pos q (Bool.and_eq_true_iff.mp (Decomposition.input_tree q d hd).1).1) m
      (checkedOrdinal q m d hd) (interpretation q e) := by
  have hnode := (Decomposition.word_spec q e he).1 s hs
  cases s with
  | parameter p => simp only [nodeCandidate, Bool.false_eq_true] at hc
  | sum a b => simp only [nodeCandidate, Bool.false_eq_true] at hc
  | theta k a =>
    have hx : k = m ∧ Comparison.equalCode q e (.theta k a : RelativeTerm Nat).code = true ∧
        Comparison.lessCode q d (Decomposition.highCode m a.code) = true := by
      simpa only [nodeCandidate, Bool.and_eq_true, beq_iff_eq] using hc
    obtain ⟨hkm, hve, hlt⟩ := hx
    subst k
    have ha := checked_theta_argument q m a hnode.1
    have hai : Decomposition.inputCheck q a.code = true :=
      (Decomposition.inputCheck_exact q a.code).mpr
        ⟨by simpa only [checkCode_code] using ha, by simpa only [ThetaCourse.rawTree_code, Comparison.Normal] using hnode.2.1⟩
    let Γ := interpretation q (Decomposition.highCode m a.code)
    let ρ := interpretation q (Decomposition.lowCode m a.code)
    let b := sourceOrdinal q m a ha
    have hηs : interpretation q e = denote q (.theta m a) := by
      simpa only [interpretation_code] using ((Comparison.equalCode_exact q e (.theta m a : RelativeTerm Nat).code).mp hve).2.2.2.2
    have hηpos : 0 < interpretation q e := hnode.2.2.1.trans_eq hηs.symm
    have hΔΓ : (checkedOrdinal q m d hd).val < Γ := by
      rw [checkedOrdinal_val]
      exact ((Comparison.lessCode_exact q d (Decomposition.highCode m a.code)).mp hlt).2.2.2.2
    have hv : b.val = Γ + ρ := by
      simpa only [b, sourceOrdinal, interpretation_code] using (Decomposition.parts_reconstruct q m a.code hai).symm
    refine ⟨b, Γ, ρ, checked_notation_at q a ha m, checked_theta_sort q m a hnode.1,
      Decomposition.highPart_dvd q m a.code hai, Decomposition.lowPart_bound q m a.code hai,
      hv, hΔΓ, ?_, (starCode_exact q m d e hd he hηpos).mp hst⟩
    simpa only [denote, eval, b, sourceOrdinal] using hηs

private theorem singleton_of_length {α : Type} (as : List α) (h : as.length = 1) : ∃ a, as = [a] := by
  cases as with
  | nil => simp at h
  | cons a as =>
    cases as with
    | nil => exact ⟨a, rfl⟩
    | cons b bs => simp at h

/-- A genuine higher presentation is detected among the actual native ANF
atoms. Principal ANF uniqueness supplies the whole-residual atom; actual
cardinal ranges identify its written level, and source collapse injection
identifies its original argument. -/
theorem higher_has_candidate (q m d e : Nat) (hd : Decomposition.inputCheck q d = true)
    (he : Decomposition.inputCheck q e = true)
    (hηlow : interpretation q e < omegaSequence (base q) (m + 1))
    (hp : SourceFixedPointLimits.GlobalHigherPresentation (base q)
      (base_pos q (Bool.and_eq_true_iff.mp (Decomposition.input_tree q d hd).1).1) m
        (checkedOrdinal q m d hd) (interpretation q e)) :
    starCode q m d e = true ∧ ∃ s ∈ Decomposition.word e, nodeCandidate q m d e s = true := by
  have hq := (Bool.and_eq_true_iff.mp (Decomposition.input_tree q d hd).1).1
  obtain ⟨b, Γ, ρ, hbm, hb, hΓ, hρ, hbe, hΔΓ, hηb, hsΔ⟩ := hp
  have hbdom := globalNotation_sorted_lt_boundary (base q) (base_pos q hq) m m le_rfl hbm hb
  have hηpos : 0 < interpretation q e := (globalCollapse_pos (base q) (base_pos q hq) m b.val hbdom).trans_eq hηb.symm
  have hηp : Ordinal.IsPrincipal (· + ·) (interpretation q e) :=
    hηb.symm ▸ globalCollapse_add_closed (base q) (base_pos q hq) m b.val hbdom
  have hbaseη : omegaSequence (base q) m ≤ interpretation q e :=
    (globalCollapse_bounds (base q) (base_pos q hq) m b.val hbdom).1.trans_eq hηb.symm
  have hw := (Decomposition.word_spec q e he).2
  rw [canonicalANF_principal hηpos hηp] at hw
  have hlength : (Decomposition.word e).length = 1 := by
    have hl := congrArg List.length hw
    simpa only [List.length_map, List.length_singleton] using hl
  obtain ⟨s, hword⟩ := singleton_of_length (Decomposition.word e) hlength
  have hs : s ∈ Decomposition.word e := by rw [hword]; exact List.mem_singleton_self _
  have hnode := (Decomposition.word_spec q e he).1 s hs
  have hsv : denote q s = interpretation q e := by
    rw [hword, List.map_cons, List.map_nil] at hw
    exact (List.cons.inj hw).1
  refine ⟨(starCode_exact q m d e hd he hηpos).mpr hsΔ, ?_⟩
  cases s with
  | parameter p =>
    have hlt := checked_parameter_lt_base q p hnode.1
    have hbase : base q ≤ denote q (.parameter p) :=
      (((omegaSequence_strictMono (base q)).monotone (Nat.zero_le m)).trans hbaseη).trans_eq hsv.symm
    exact False.elim (hlt.not_ge hbase)
  | sum a a' =>
    have hshape := Comparison.atoms_shape (ThetaCourse.rawTree e) (.sum a a') hs
    rcases hshape with ⟨p, hh⟩ | ⟨k, z, hh⟩ <;> cases hh
  | theta k a =>
    have hrange := checked_theta_range q k a hnode.1
    have hkm : k = m := by
      rcases lt_trichotomy k m with hkm | hkm | hmk
      · have hbad : denote q (.theta k a) < interpretation q e := hrange.2.trans_le
          (((omegaSequence_strictMono (base q)).monotone (Nat.succ_le_of_lt hkm)).trans hbaseη)
        exact False.elim (hbad.ne hsv)
      · exact hkm
      · have hbad : omegaSequence (base q) (m + 1) ≤ interpretation q e :=
          (((omegaSequence_strictMono (base q)).monotone (Nat.succ_le_of_lt hmk)).trans hrange.1).trans_eq hsv
        exact False.elim (hηlow.not_ge hbad)
    subst k
    have ha := checked_theta_argument q m a hnode.1
    have hai : Decomposition.inputCheck q a.code = true :=
      (Decomposition.inputCheck_exact q a.code).mpr
        ⟨by simpa only [checkCode_code] using ha, by simpa only [ThetaCourse.rawTree_code, Comparison.Normal] using hnode.2.1⟩
    have hasort := checked_theta_sort q m a hnode.1
    let an := sourceOrdinal q m a ha
    have hab : an.val = b.val := (globalCollapse_eq_iff (base q) (base_pos q hq) m an b hasort hb).mp
      (by simpa only [denote, eval, an, sourceOrdinal] using hsv.trans hηb)
    have hhigh : interpretation q (Decomposition.highCode m a.code) = Γ := by
      rw [(Decomposition.parts_code_value q m a.code hai).1, interpretation_code]
      change omegaSequence (base q) (m + 1) * (an.val / omegaSequence (base q) (m + 1)) = Γ
      rw [hab, hbe]
      obtain ⟨δ, hδ⟩ := hΓ
      rw [hδ, Ordinal.mul_add_div _ (SourceFixedPointLimits.next_cardinal_pos (base q) (base_pos q hq) m).ne',
        Ordinal.div_eq_zero_of_lt hρ, add_zero]
    have hparts := Decomposition.parts_accepted q m a.code hai
    have hsCode : Comparison.acceptedCode q (.theta m a : RelativeTerm Nat).code = true :=
      (Comparison.acceptedCode_exact q _).mpr
        ⟨by simpa only [checkCode_code] using hnode.1, by simpa only [ThetaCourse.rawTree_code, Comparison.Normal] using hnode.2.1⟩
    have hEq : Comparison.equalCode q e (.theta m a : RelativeTerm Nat).code = true :=
      (Comparison.equalCode_exact q e _).mpr
        ⟨((Decomposition.inputCheck_exact q e).mp he).1, ((Decomposition.inputCheck_exact q e).mp he).2,
          ((Comparison.acceptedCode_exact q _).mp hsCode).1, ((Comparison.acceptedCode_exact q _).mp hsCode).2,
          by simpa only [interpretation_code] using hsv.symm⟩
    have hLt : Comparison.lessCode q d (Decomposition.highCode m a.code) = true :=
      (Comparison.lessCode_exact q d _).mpr
        ⟨((Decomposition.inputCheck_exact q d).mp hd).1, ((Decomposition.inputCheck_exact q d).mp hd).2,
          ((Comparison.acceptedCode_exact q _).mp hparts.1).1, ((Comparison.acceptedCode_exact q _).mp hparts.1).2,
          by simpa only [checkedOrdinal_val, hhigh] using hΔΓ⟩
    exact ⟨.theta m a, hs, by simp only [nodeCandidate, beq_self_eq_true, hEq, hLt, Bool.true_and]⟩

theorem higherCheck_exact (q m d e : Nat) (hd : Decomposition.inputCheck q d = true)
    (he : Decomposition.inputCheck q e = true)
    (hηlow : interpretation q e < omegaSequence (base q) (m + 1)) :
    higherCheck q m d e = true ↔ SourceFixedPointLimits.GlobalHigherPresentation (base q)
      (base_pos q (Bool.and_eq_true_iff.mp (Decomposition.input_tree q d hd).1).1) m
        (checkedOrdinal q m d hd) (interpretation q e) := by
  rw [higherCheck, Bool.and_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨hst, s, hs, hc⟩
    exact nodeCandidate_higher q m d e hd he s hs hc hst
  · exact higher_has_candidate q m d e hd he hηlow

def fixedCode (q m c : Nat) : Bool := inputCheck q m c &&
  (zeroCheck (Decomposition.lowCode m c) || higherCheck q m (Decomposition.highCode m c) (Decomposition.lowCode m c))

def strictCode (q m c : Nat) : Bool := inputCheck q m c && !fixedCode q m c

theorem fixedCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => fixedCode p.1 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Nat × (Nat × Nat) => Decomposition.highCode p.2.1 p.2.2) := Decomposition.highCode_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have he : Primrec (fun p : Nat × (Nat × Nat) => Decomposition.lowCode p.2.1 p.2.2) := Decomposition.lowCode_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp inputCheck_primrec (Primrec.or.comp (zeroCheck_primrec.comp he)
    (higherCheck_primrec.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair (hd.pair he)))))

theorem strictCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => strictCode p.1 p.2.1 p.2.2) :=
  Primrec.and.comp inputCheck_primrec (Primrec.not.comp fixedCode_primrec)

noncomputable def delta (q m c : Nat) : Ordinal.{0} :=
  omegaSequence (base q) (m + 1) * (interpretation q c / omegaSequence (base q) (m + 1))

noncomputable def residual (q m c : Nat) : Ordinal.{0} := interpretation q c % omegaSequence (base q) (m + 1)

def SourceFixed (q m c : Nat) : Prop :=
  SourceFixedPointLimits.globalResidualImageSup (base q) m (delta q m c) (residual q m c) = residual q m c

def SourceStrict (q m c : Nat) : Prop :=
  residual q m c < SourceFixedPointLimits.globalResidualImageSup (base q) m (delta q m c) (residual q m c)

/-- Both ordinary-supremum boundary clauses are carried through the actual
source theorem. Only its base-1 clause is then excluded by the original
native epsilon-base equation. Higher sufficiency derives equality directly;
no limit classifier is supplied to the executing recognizer. -/
theorem fixed_parts_iff (q m c : Nat) (hc : inputCheck q m c = true) :
    SourceFixed q m c ↔ interpretation q (Decomposition.lowCode m c) = 0 ∨
      SourceFixedPointLimits.GlobalHigherPresentation (base q)
        (base_pos q (Bool.and_eq_true_iff.mp (Decomposition.input_tree q c (Bool.and_eq_true_iff.mp hc).1).1).1) m
        (checkedOrdinal q m (Decomposition.highCode m c) (Decomposition.parts_accepted q m c (Bool.and_eq_true_iff.mp hc).1).1)
        (interpretation q (Decomposition.lowCode m c)) := by
  have hi := (Bool.and_eq_true_iff.mp hc).1
  have hs := (inputCheck_exact q m c).mp hc
  have hq := (Bool.and_eq_true_iff.mp (Decomposition.input_tree q c hi).1).1
  have hparts := Decomposition.parts_accepted q m c hi
  let d := Decomposition.highCode m c
  let e := Decomposition.lowCode m c
  have hd : Decomposition.inputCheck q d = true := hparts.1
  have he : Decomposition.inputCheck q e = true := hparts.2
  let dn := checkedOrdinal q m d hd
  have hdSort : dn.val < omegaSequence (base q) (m + 2) := by
    rw [checkedOrdinal_val, (Decomposition.parts_code_value q m c hi).1]
    exact (Ordinal.mul_div_le _ _).trans_lt hs.2.2
  have hddvd : omegaSequence (base q) (m + 1) ∣ dn.val := by
    rw [checkedOrdinal_val]
    exact Decomposition.highPart_dvd q m c hi
  have heLow := Decomposition.lowPart_bound q m c hi
  have harg : GlobalNotation (base q) m (dn.val + interpretation q e) := by
    rw [checkedOrdinal_val, Decomposition.parts_reconstruct q m c hi]
    rw [Decomposition.input_value q c hi]
    exact checked_notation_at q _ (Decomposition.input_tree q c hi).1 m
  have hcriterion := SourceFixedPointLimits.global_source_argument_fixed_iff (base q) (base_pos q hq)
    m dn hdSort hddvd (interpretation q e) heLow harg
  have hvalue := Decomposition.parts_code_value q m c hi
  change SourceFixed q m c ↔ interpretation q e = 0 ∨ _
  unfold SourceFixed delta residual
  rw [← hvalue.1, ← hvalue.2]
  constructor
  · intro hfixed
    rcases hcriterion.mp hfixed with hz | hb | ⟨hl, hp⟩
    · exact Or.inl hz
    · exact False.elim (base_ne_one q hq hb.2.2.1)
    · exact Or.inr hp
  · rintro (hz | hp)
    · exact hcriterion.mpr (Or.inl hz)
    · exact SourceFixedPointLimits.global_higherPresentation_fixed (base q) (base_pos q hq)
        m dn hdSort hddvd (interpretation q e) heLow hp

theorem fixedCode_correct (q m c : Nat) (hc : inputCheck q m c = true) :
    fixedCode q m c = true ↔ SourceFixed q m c := by
  have hi := (Bool.and_eq_true_iff.mp hc).1
  have hparts := Decomposition.parts_accepted q m c hi
  rw [fixedCode, hc, Bool.true_and, Bool.or_eq_true,
    zeroCheck_exact q _ hparts.2,
    higherCheck_exact q m _ _ hparts.1 hparts.2 (Decomposition.lowPart_bound q m c hi)]
  exact (fixed_parts_iff q m c hc).symm

theorem strictCode_correct (q m c : Nat) (hc : inputCheck q m c = true) :
    strictCode q m c = true ↔ SourceStrict q m c := by
  have hi := (Bool.and_eq_true_iff.mp hc).1
  have hs := (inputCheck_exact q m c).mp hc
  have hparts := Decomposition.parts_accepted q m c hi
  have hd : Decomposition.inputCheck q (Decomposition.highCode m c) = true := hparts.1
  let dn := checkedOrdinal q m (Decomposition.highCode m c) hd
  have hq := (Bool.and_eq_true_iff.mp (Decomposition.input_tree q c hi).1).1
  have hdSort : dn.val < omegaSequence (base q) (m + 2) := by
    rw [checkedOrdinal_val, (Decomposition.parts_code_value q m c hi).1]
    exact (Ordinal.mul_div_le _ _).trans_lt hs.2.2
  have hddvd : omegaSequence (base q) (m + 1) ∣ dn.val := by
    rw [checkedOrdinal_val]
    exact Decomposition.highPart_dvd q m c hi
  have heLow := Decomposition.lowPart_bound q m c hi
  have hstrict := SourceFixedPointLimits.global_strict_sup_iff_not_fixed (base q) (base_pos q hq)
    m dn hdSort hddvd (interpretation q (Decomposition.lowCode m c)) heLow
  rw [checkedOrdinal_val, (Decomposition.parts_code_value q m c hi).1,
    (Decomposition.parts_code_value q m c hi).2] at hstrict
  have hb : ((!fixedCode q m c) = true) ↔ ¬ (fixedCode q m c = true) := by
    cases fixedCode q m c <;> decide
  rw [strictCode, hc, Bool.true_and, hb, fixedCode_correct q m c hc]
  exact hstrict.symm

theorem fixedCode_exact (q m c : Nat) : fixedCode q m c = true ↔
    inputCheck q m c = true ∧ SourceFixed q m c := by
  constructor
  · intro h
    have hc := (Bool.and_eq_true_iff.mp h).1
    exact ⟨hc, (fixedCode_correct q m c hc).mp h⟩
  · rintro ⟨hc, hp⟩
    exact (fixedCode_correct q m c hc).mpr hp

theorem strictCode_exact (q m c : Nat) : strictCode q m c = true ↔
    inputCheck q m c = true ∧ SourceStrict q m c := by
  constructor
  · intro h
    have hc := (Bool.and_eq_true_iff.mp h).1
    exact ⟨hc, (strictCode_correct q m c hc).mp h⟩
  · rintro ⟨hc, hp⟩
    exact (strictCode_correct q m c hc).mpr hp

/-- The raw domain admits every original native term with the actual source
argument sort. Weak normality is constructed by genuine normalization. -/
def rawInputCheck (q m c : Nat) : Bool := checkCode q c && decide ((ThetaCourse.rawTree c).outerSort ≤ m + 2)

theorem rawInputCheck_primrec : Primrec (fun p : Nat × (Nat × Nat) => rawInputCheck p.1 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : Nat × (Nat × Nat) => checkCode p.1 p.2.2) :=
    checkCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun p : Nat × (Nat × Nat) => (ThetaCourse.rawTree p.2.2).outerSort) :=
    outerSort_primrec.comp (ThetaCourse.rawTree_primrec.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.and.comp hc ((Primrec.nat_le.comp hs
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2))).decide)

theorem rawInputCheck_exact (q m c : Nat) : rawInputCheck q m c = true ↔
    checkCode q c = true ∧ interpretation q c < omegaSequence (base q) (m + 2) := by
  simp only [rawInputCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hs⟩
    obtain ⟨t, ht, hct⟩ := (checkCode_exact q c).mp hc
    exact ⟨hc, by simpa only [← ht, interpretation_code, ThetaCourse.rawTree_code] using
      ((denote_lt_iff_outerSort_le q t hct (m + 2) (by omega)).mpr
        (by simpa only [← ht, ThetaCourse.rawTree_code] using hs))⟩
  · rintro ⟨hc, hs⟩
    obtain ⟨t, ht, hct⟩ := (checkCode_exact q c).mp hc
    exact ⟨hc, by simpa only [← ht, ThetaCourse.rawTree_code] using
      ((denote_lt_iff_outerSort_le q t hct (m + 2) (by omega)).mp
        (by simpa only [← ht, interpretation_code] using hs))⟩

theorem normalized_input (q m c : Nat) (hc : rawInputCheck q m c = true) :
    inputCheck q m (Normalization.normalizeCode q c) = true := by
  have hs := (rawInputCheck_exact q m c).mp hc
  have hn := Normalization.normalizeCode_checked q c hs.1
  exact (inputCheck_exact q m _).mpr ⟨hn.1, hn.2.1, hn.2.2.trans_lt hs.2⟩

def fixedRawCode (q m c : Nat) : Bool := rawInputCheck q m c && fixedCode q m (Normalization.normalizeCode q c)

def strictRawCode (q m c : Nat) : Bool := rawInputCheck q m c && strictCode q m (Normalization.normalizeCode q c)

theorem fixedRawCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => fixedRawCode p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : Nat × (Nat × Nat) => Normalization.normalizeCode p.1 p.2.2) := Normalization.Effective.normalizeCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp rawInputCheck_primrec
    (fixedCode_primrec.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair hn)))

theorem strictRawCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => strictRawCode p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : Nat × (Nat × Nat) => Normalization.normalizeCode p.1 p.2.2) := Normalization.Effective.normalizeCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp rawInputCheck_primrec
    (strictCode_primrec.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair hn)))

theorem fixedRawCode_exact (q m c : Nat) : fixedRawCode q m c = true ↔
    checkCode q c = true ∧ interpretation q c < omegaSequence (base q) (m + 2) ∧ SourceFixed q m c := by
  constructor
  · intro h
    obtain ⟨hc, hf⟩ := Bool.and_eq_true_iff.mp h
    have hs := (rawInputCheck_exact q m c).mp hc
    have hn := Normalization.normalizeCode_checked q c hs.1
    have hp := (fixedCode_correct q m _ (normalized_input q m c hc)).mp hf
    rw [SourceFixed, delta, residual, hn.2.2] at hp
    exact ⟨hs.1, hs.2, hp⟩
  · rintro ⟨hc, hs, hp⟩
    have hi := (rawInputCheck_exact q m c).mpr ⟨hc, hs⟩
    have hn := Normalization.normalizeCode_checked q c hc
    apply Bool.and_eq_true_iff.mpr
    refine ⟨hi, (fixedCode_correct q m _ (normalized_input q m c hi)).mpr ?_⟩
    unfold SourceFixed delta residual
    rw [hn.2.2]
    exact hp

theorem strictRawCode_exact (q m c : Nat) : strictRawCode q m c = true ↔
    checkCode q c = true ∧ interpretation q c < omegaSequence (base q) (m + 2) ∧ SourceStrict q m c := by
  constructor
  · intro h
    obtain ⟨hc, hf⟩ := Bool.and_eq_true_iff.mp h
    have hs := (rawInputCheck_exact q m c).mp hc
    have hn := Normalization.normalizeCode_checked q c hs.1
    have hp := (strictCode_correct q m _ (normalized_input q m c hc)).mp hf
    rw [SourceStrict, delta, residual, hn.2.2] at hp
    exact ⟨hs.1, hs.2, hp⟩
  · rintro ⟨hc, hs, hp⟩
    have hi := (rawInputCheck_exact q m c).mpr ⟨hc, hs⟩
    have hn := Normalization.normalizeCode_checked q c hc
    apply Bool.and_eq_true_iff.mpr
    refine ⟨hi, (strictCode_correct q m _ (normalized_input q m c hi)).mpr ?_⟩
    unfold SourceStrict delta residual
    rw [hn.2.2]
    exact hp

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.FixedPoint
