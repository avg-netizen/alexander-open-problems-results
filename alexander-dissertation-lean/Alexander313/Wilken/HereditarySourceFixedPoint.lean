import Alexander313.Wilken.HereditarySourceFixedPointSupport
import Alexander313.Wilken.HereditarySourceDecomposition

/-!
# Executing repaired public fixed-point and strict supremum tests

The original checked weak-normal public argument is split by the actual
cardinal ANF cut. A real public ANF atom is a higher presentation only when
it is a literal theta-m node equal to the WHOLE residual, its actual divided
high part exceeds Delta, and the literal exposed Delta star is below eta.
The original same-level argument and all theta sorts are inherited from
public admission. Both the zero branch and the unique base-one unit branch
are explicit. Strict supremum comparison uses the proved actual domination.
No fixed-point, parser, normalization, comparison or effectivity oracle is
supplied. These primitive-recursive proof candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceFixedPoint

private theorem rawLess_correct (r c d : Nat)
    (hc : SourceDecomposition.inputCheck r c = true) (hd : SourceDecomposition.inputCheck r d = true) :
    Theta.lessCode r c d = true ↔ interpretation r c < interpretation r d := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_iff r c).mp ((SourceDecomposition.inputCheck_exact r c).mp hc).1
  obtain ⟨u, rfl, hu⟩ := (checkCode_iff r d).mp ((SourceDecomposition.inputCheck_exact r d).mp hd).1
  have hnt : Theta.Normal r t := by simpa only [ThetaCourse.rawTree_code] using
    ((SourceDecomposition.inputCheck_exact r t.code).mp hc).2
  have hnu : Theta.Normal r u := by simpa only [ThetaCourse.rawTree_code] using
    ((SourceDecomposition.inputCheck_exact r u.code).mp hd).2
  simpa only [Theta.lessCode_code, interpretation_code] using Theta.less_correct r t u ht hu hnt hnu

private theorem rawEqual_correct (r c d : Nat)
    (hc : SourceDecomposition.inputCheck r c = true) (hd : SourceDecomposition.inputCheck r d = true) :
    Theta.equalCode r c d = true ↔ interpretation r c = interpretation r d := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_iff r c).mp ((SourceDecomposition.inputCheck_exact r c).mp hc).1
  obtain ⟨u, rfl, hu⟩ := (checkCode_iff r d).mp ((SourceDecomposition.inputCheck_exact r d).mp hd).1
  have hnt : Theta.Normal r t := by simpa only [ThetaCourse.rawTree_code] using
    ((SourceDecomposition.inputCheck_exact r t.code).mp hc).2
  have hnu : Theta.Normal r u := by simpa only [ThetaCourse.rawTree_code] using
    ((SourceDecomposition.inputCheck_exact r u.code).mp hd).2
  simpa only [Theta.equalCode_code, interpretation_code] using Theta.equal_correct r t u ht hu hnt hnu

def lessCode (r c d : Nat) : Bool :=
  (SourceDecomposition.inputCheck r c && SourceDecomposition.inputCheck r d) && Theta.lessCode r c d

def equalCode (r c d : Nat) : Bool :=
  (SourceDecomposition.inputCheck r c && SourceDecomposition.inputCheck r d) && Theta.equalCode r c d

theorem lessCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => lessCode p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (Primrec.and.comp
    (SourceDecomposition.inputCheck_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (SourceDecomposition.inputCheck_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))) Theta.Effective.lessCode_primrec

theorem equalCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => equalCode p.1 p.2.1 p.2.2) :=
  Primrec.and.comp (Primrec.and.comp
    (SourceDecomposition.inputCheck_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (SourceDecomposition.inputCheck_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))) Theta.Effective.equalCode_primrec

theorem lessCode_exact (r c d : Nat) : lessCode r c d = true ↔
    checkCode r c = true ∧ Theta.Normal r (ThetaCourse.rawTree c) ∧
      checkCode r d = true ∧ Theta.Normal r (ThetaCourse.rawTree d) ∧ interpretation r c < interpretation r d := by
  constructor
  · intro h
    obtain ⟨hs, hv⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hc, hd⟩ := Bool.and_eq_true_iff.mp hs
    have hsc := (SourceDecomposition.inputCheck_exact r c).mp hc
    have hsd := (SourceDecomposition.inputCheck_exact r d).mp hd
    exact ⟨hsc.1, hsc.2, hsd.1, hsd.2, (rawLess_correct r c d hc hd).mp hv⟩
  · rintro ⟨hc, hnc, hd, hnd, hv⟩
    have hsc := (SourceDecomposition.inputCheck_exact r c).mpr ⟨hc, hnc⟩
    have hsd := (SourceDecomposition.inputCheck_exact r d).mpr ⟨hd, hnd⟩
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hsc, hsd⟩, (rawLess_correct r c d hsc hsd).mpr hv⟩

theorem equalCode_exact (r c d : Nat) : equalCode r c d = true ↔
    checkCode r c = true ∧ Theta.Normal r (ThetaCourse.rawTree c) ∧
      checkCode r d = true ∧ Theta.Normal r (ThetaCourse.rawTree d) ∧ interpretation r c = interpretation r d := by
  constructor
  · intro h
    obtain ⟨hs, hv⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hc, hd⟩ := Bool.and_eq_true_iff.mp hs
    have hsc := (SourceDecomposition.inputCheck_exact r c).mp hc
    have hsd := (SourceDecomposition.inputCheck_exact r d).mp hd
    exact ⟨hsc.1, hsc.2, hsd.1, hsd.2, (rawEqual_correct r c d hc hd).mp hv⟩
  · rintro ⟨hc, hnc, hd, hnd, hv⟩
    have hsc := (SourceDecomposition.inputCheck_exact r c).mpr ⟨hc, hnc⟩
    have hsd := (SourceDecomposition.inputCheck_exact r d).mpr ⟨hd, hnd⟩
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hsc, hsd⟩, (rawEqual_correct r c d hsc hsd).mpr hv⟩

def nodeCandidate (r m d e : Nat) : RelativeTerm Nat → Bool
  | .theta k a => (k == m) && (equalCode r e (.theta k a : RelativeTerm Nat).code &&
      lessCode r d (SourceDecomposition.highCode r m a.code))
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

private def candidateNumeric (r m d e : Nat) (s : RelativeTerm Nat) : Bool :=
  cond (nodeTag s == 2) ((nodeIndex s == m) && (equalCode r e s.code &&
    lessCode r d (SourceDecomposition.highCode r m (nodeArgument s)))) false

private theorem candidateNumeric_eq (r m d e : Nat) (s : RelativeTerm Nat) :
    candidateNumeric r m d e s = nodeCandidate r m d e s := by
  cases s <;> simp [candidateNumeric, nodeCandidate, nodeTag, nodeIndex, nodeArgument,
    RelativeTerm.code, Nat.unpair_pair]

theorem nodeCandidate_primrec : Primrec (fun p : Nat × (Nat × (Nat × (Nat × RelativeTerm Nat))) =>
    nodeCandidate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hq : Primrec (fun p : Nat × (Nat × (Nat × (Nat × RelativeTerm Nat))) => p.1) := Primrec.fst
  have hm : Primrec (fun p : Nat × (Nat × (Nat × (Nat × RelativeTerm Nat))) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat × (Nat × (Nat × (Nat × RelativeTerm Nat))) => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have he : Primrec (fun p : Nat × (Nat × (Nat × (Nat × RelativeTerm Nat))) => p.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hs : Primrec (fun p : Nat × (Nat × (Nat × (Nat × RelativeTerm Nat))) => p.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hhigh := SourceDecomposition.highCode_primrec.comp (hq.pair (hm.pair (nodeArgument_primrec.comp hs)))
  have h := (Primrec.beq.comp (nodeTag_primrec.comp hs) (Primrec.const 2)).cond
    (Primrec.and.comp (Primrec.beq.comp (nodeIndex_primrec.comp hs) hm)
      (Primrec.and.comp (equalCode_primrec.comp (hq.pair (he.pair (code_primrec.comp hs))))
        (lessCode_primrec.comp (hq.pair (hd.pair hhigh))))) (Primrec.const false)
  change Primrec (fun p : Nat × (Nat × (Nat × (Nat × RelativeTerm Nat))) =>
    candidateNumeric p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) at h
  simpa only [candidateNumeric_eq] using h

def starCode (r m d e : Nat) : Bool := starLess r m (ThetaCourse.rawTree d) (ThetaCourse.rawTree e)

theorem starCode_primrec : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => starCode p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  starLess_primrec.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
    ((ThetaCourse.rawTree_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
      (ThetaCourse.rawTree_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))

def higherCheck (r m d e : Nat) : Bool := starCode r m d e &&
  (SourceDecomposition.word r e).any (nodeCandidate r m d e)

theorem higherCheck_primrec : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => higherCheck p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have htest : Primrec₂ (fun p : Nat × (Nat × (Nat × Nat)) =>
      fun s : RelativeTerm Nat => nodeCandidate p.1 p.2.1 p.2.2.1 p.2.2.2 s) :=
    (nodeCandidate_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
          ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd))))).to₂
  have hany := (SourceOne.Comparison.Effective.listAny_primrec _ htest).comp Primrec.id
    (SourceDecomposition.word_primrec.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.and.comp starCode_primrec hany

def zeroCheck (r e : Nat) : Bool := (SourceDecomposition.word r e).length == 0

theorem zeroCheck_primrec : Primrec₂ zeroCheck :=
  (Primrec.beq.comp (Primrec.list_length.comp SourceDecomposition.word_primrec) (Primrec.const 0)).to₂

theorem zeroCheck_exact (r e : Nat) (he : SourceDecomposition.inputCheck r e = true) :
    zeroCheck r e = true ↔ interpretation r e = 0 := by
  have hv : principalSum ((SourceDecomposition.word r e).map (denote r)) = interpretation r e := by
    rw [(SourceDecomposition.word_spec r e he).2, principalSum_canonicalANF]
  cases hw : SourceDecomposition.word r e with
  | nil =>
    have hz : interpretation r e = 0 := by rw [← hv, hw]; rfl
    simp [zeroCheck, hw, hz]
  | cons a as =>
    have ha := (SourceDecomposition.word_spec r e he).1 a (by rw [hw]; exact List.mem_cons_self)
    have hp : 0 < interpretation r e := by rw [← hv, hw]; exact ha.2.2.1.trans_le le_self_add
    simp [zeroCheck, hw, ne_of_gt hp]

def inputCheck (r m c : Nat) : Bool := SourceDecomposition.inputCheck r c &&
  decide ((ThetaCourse.rawTree c).outerSort ≤ m + 2)

theorem inputCheck_primrec : Primrec (fun p : Nat × (Nat × Nat) => inputCheck p.1 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : Nat × (Nat × Nat) => SourceDecomposition.inputCheck p.1 p.2.2) := SourceDecomposition.inputCheck_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun p : Nat × (Nat × Nat) => (ThetaCourse.rawTree p.2.2).outerSort) :=
    outerSort_primrec.comp (ThetaCourse.rawTree_primrec.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.and.comp hc ((Primrec.nat_le.comp hs
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2))).decide)

theorem inputCheck_exact (r m c : Nat) : inputCheck r m c = true ↔
    checkCode r c = true ∧ Theta.Normal r (ThetaCourse.rawTree c) ∧
      interpretation r c < omegaSequence (finiteBase r) (m + 2) := by
  simp only [inputCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hs⟩
    have ht := SourceDecomposition.input_tree r c hc
    exact ⟨((SourceDecomposition.inputCheck_exact r c).mp hc).1, ht.2,
      (SourceDecomposition.input_value r c hc).trans_lt
        ((denote_lt_iff_outerSort_le r _ ht.1 (m + 2) (by omega)).mpr hs)⟩
  · rintro ⟨hc, hn, hs⟩
    have hd := (SourceDecomposition.inputCheck_exact r c).mpr ⟨hc, hn⟩
    refine ⟨hd, (denote_lt_iff_outerSort_le r _ (SourceDecomposition.input_tree r c hd).1 (m + 2) (by omega)).mp ?_⟩
    exact (SourceDecomposition.input_value r c hd).symm.trans_lt hs

noncomputable def checkedOrdinal (r m c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    GlobalNotationOrdinal (finiteBase r) (m + 1) :=
  sourceOrdinal r m (ThetaCourse.rawTree c) (SourceDecomposition.input_tree r c hc).1

@[simp] theorem checkedOrdinal_val (r m c : Nat) (hc : SourceDecomposition.inputCheck r c = true) :
    (checkedOrdinal r m c hc).val = interpretation r c := (SourceDecomposition.input_value r c hc).symm

theorem starCode_exact (r m d e : Nat) (hd : SourceDecomposition.inputCheck r d = true)
    (he : SourceDecomposition.inputCheck r e = true) (hepos : 0 < interpretation r e) :
    starCode r m d e = true ↔ globalStar (finiteBase r)
      (finiteBase_pos r) m
        (checkedOrdinal r m d hd) < interpretation r e := by
  have hdt := SourceDecomposition.input_tree r d hd
  have het := SourceDecomposition.input_tree r e he
  have hpos : 0 < denote r (ThetaCourse.rawTree e) :=
    hepos.trans_eq (SourceDecomposition.input_value r e he)
  simpa only [starCode, checkedOrdinal, ← SourceDecomposition.input_value r e he] using
    starLess_exact r m _ _ hdt.1 het.1 hdt.2 het.2 hpos

theorem nodeCandidate_higher (r m d e : Nat) (hd : SourceDecomposition.inputCheck r d = true)
    (he : SourceDecomposition.inputCheck r e = true) (s : RelativeTerm Nat)
    (hs : s ∈ SourceDecomposition.word r e) (hc : nodeCandidate r m d e s = true)
    (hst : starCode r m d e = true) :
    SourceFixedPointLimits.GlobalHigherPresentation (finiteBase r)
      (finiteBase_pos r) m
      (checkedOrdinal r m d hd) (interpretation r e) := by
  have hnode := (SourceDecomposition.word_spec r e he).1 s hs
  cases s with
  | parameter p => simp only [nodeCandidate, Bool.false_eq_true] at hc
  | sum a b => simp only [nodeCandidate, Bool.false_eq_true] at hc
  | theta k a =>
    have hx : k = m ∧ equalCode r e (.theta k a : RelativeTerm Nat).code = true ∧
        lessCode r d (SourceDecomposition.highCode r m a.code) = true := by
      simpa only [nodeCandidate, Bool.and_eq_true, beq_iff_eq] using hc
    obtain ⟨hkm, hve, hlt⟩ := hx
    subst k
    have ha := checked_theta_argument r m a hnode.1
    have hai : SourceDecomposition.inputCheck r a.code = true :=
      (SourceDecomposition.inputCheck_exact r a.code).mpr
        ⟨by simpa only [checkCode_code] using ha,
          by simpa only [ThetaCourse.rawTree_code] using (Theta.normal_theta r m a).mp hnode.2.1⟩
    let Γ := interpretation r (SourceDecomposition.highCode r m a.code)
    let ρ := interpretation r (SourceDecomposition.lowCode r m a.code)
    let b := sourceOrdinal r m a ha
    have hηs : interpretation r e = denote r (.theta m a) := by
      simpa only [interpretation_code] using ((equalCode_exact r e (.theta m a : RelativeTerm Nat).code).mp hve).2.2.2.2
    have hηpos : 0 < interpretation r e := hnode.2.2.1.trans_eq hηs.symm
    have hΔΓ : (checkedOrdinal r m d hd).val < Γ := by
      rw [checkedOrdinal_val]
      exact ((lessCode_exact r d (SourceDecomposition.highCode r m a.code)).mp hlt).2.2.2.2
    have hv : b.val = Γ + ρ := by
      simpa only [b, sourceOrdinal, interpretation_code] using (SourceDecomposition.parts_reconstruct r m a.code hai).symm
    refine ⟨b, Γ, ρ, checked_notation_at r a ha m, checked_theta_sort r m a hnode.1,
      SourceDecomposition.highPart_dvd r m a.code hai, SourceDecomposition.lowPart_bound r m a.code hai,
      hv, hΔΓ, ?_, (starCode_exact r m d e hd he hηpos).mp hst⟩
    simpa only [denote, eval, b, sourceOrdinal] using hηs

private theorem singleton_of_length {α : Type} (as : List α) (h : as.length = 1) : ∃ a, as = [a] := by
  cases as with
  | nil => simp at h
  | cons a as =>
    cases as with
    | nil => exact ⟨a, rfl⟩
    | cons b bs => simp at h

/-- A genuine higher presentation is detected among the actual public ANF
atoms. Principal ANF uniqueness supplies the whole-residual atom; actual
cardinal ranges identify its written level, and source collapse injection
identifies its original argument. -/
theorem higher_has_candidate (r m d e : Nat) (hd : SourceDecomposition.inputCheck r d = true)
    (he : SourceDecomposition.inputCheck r e = true)
    (hηlow : interpretation r e < omegaSequence (finiteBase r) (m + 1))
    (hp : SourceFixedPointLimits.GlobalHigherPresentation (finiteBase r)
      (finiteBase_pos r) m
        (checkedOrdinal r m d hd) (interpretation r e)) :
    starCode r m d e = true ∧ ∃ s ∈ SourceDecomposition.word r e, nodeCandidate r m d e s = true := by
  obtain ⟨b, Γ, ρ, hbm, hb, hΓ, hρ, hbe, hΔΓ, hηb, hsΔ⟩ := hp
  have hbdom := globalNotation_sorted_lt_boundary (finiteBase r) (finiteBase_pos r) m m le_rfl hbm hb
  have hηpos : 0 < interpretation r e := (globalCollapse_pos (finiteBase r) (finiteBase_pos r) m b.val hbdom).trans_eq hηb.symm
  have hηp : Ordinal.IsPrincipal (· + ·) (interpretation r e) :=
    hηb.symm ▸ globalCollapse_add_closed (finiteBase r) (finiteBase_pos r) m b.val hbdom
  have hbaseη : omegaSequence (finiteBase r) m ≤ interpretation r e :=
    (globalCollapse_bounds (finiteBase r) (finiteBase_pos r) m b.val hbdom).1.trans_eq hηb.symm
  have hw := (SourceDecomposition.word_spec r e he).2
  rw [canonicalANF_principal hηpos hηp] at hw
  have hlength : (SourceDecomposition.word r e).length = 1 := by
    have hl := congrArg List.length hw
    simpa only [List.length_map, List.length_singleton] using hl
  obtain ⟨s, hword⟩ := singleton_of_length (SourceDecomposition.word r e) hlength
  have hs : s ∈ SourceDecomposition.word r e := by rw [hword]; exact List.mem_singleton_self _
  have hnode := (SourceDecomposition.word_spec r e he).1 s hs
  have hsv : denote r s = interpretation r e := by
    rw [hword, List.map_cons, List.map_nil] at hw
    exact (List.cons.inj hw).1
  refine ⟨(starCode_exact r m d e hd he hηpos).mpr hsΔ, ?_⟩
  cases s with
  | parameter p =>
    have hlt := checked_parameter_lt_base r p hnode.1
    have hbase : finiteBase r ≤ denote r (.parameter p) :=
      (((omegaSequence_strictMono (finiteBase r)).monotone (Nat.zero_le m)).trans hbaseη).trans_eq hsv.symm
    exact False.elim (hlt.not_ge hbase)
  | sum a a' =>
    have hshape := SourceDecomposition.word_shape r e (.sum a a') hs
    rcases hshape with ⟨p, hh⟩ | ⟨k, z, hh⟩ <;> cases hh
  | theta k a =>
    have hrange := checked_theta_range r k a hnode.1
    have hkm : k = m := by
      rcases lt_trichotomy k m with hkm | hkm | hmk
      · have hbad : denote r (.theta k a) < interpretation r e := hrange.2.trans_le
          (((omegaSequence_strictMono (finiteBase r)).monotone (Nat.succ_le_of_lt hkm)).trans hbaseη)
        exact False.elim (hbad.ne hsv)
      · exact hkm
      · have hbad : omegaSequence (finiteBase r) (m + 1) ≤ interpretation r e :=
          (((omegaSequence_strictMono (finiteBase r)).monotone (Nat.succ_le_of_lt hmk)).trans hrange.1).trans_eq hsv
        exact False.elim (hηlow.not_ge hbad)
    subst k
    have ha := checked_theta_argument r m a hnode.1
    have hai : SourceDecomposition.inputCheck r a.code = true :=
      (SourceDecomposition.inputCheck_exact r a.code).mpr
        ⟨by simpa only [checkCode_code] using ha,
          by simpa only [ThetaCourse.rawTree_code] using (Theta.normal_theta r m a).mp hnode.2.1⟩
    have hasort := checked_theta_sort r m a hnode.1
    let an := sourceOrdinal r m a ha
    have hab : an.val = b.val := (globalCollapse_eq_iff (finiteBase r) (finiteBase_pos r) m an b hasort hb).mp
      (by simpa only [denote, eval, an, sourceOrdinal] using hsv.trans hηb)
    have hhigh : interpretation r (SourceDecomposition.highCode r m a.code) = Γ := by
      rw [(SourceDecomposition.parts_code_value r m a.code hai).1, interpretation_code]
      change omegaSequence (finiteBase r) (m + 1) * (an.val / omegaSequence (finiteBase r) (m + 1)) = Γ
      rw [hab, hbe]
      obtain ⟨δ, hδ⟩ := hΓ
      rw [hδ, Ordinal.mul_add_div _ (SourceFixedPointLimits.next_cardinal_pos (finiteBase r) (finiteBase_pos r) m).ne',
        Ordinal.div_eq_zero_of_lt hρ, add_zero]
    have hparts := SourceDecomposition.parts_accepted r m a.code hai
    have hsCode : Theta.acceptedCode r (.theta m a : RelativeTerm Nat).code = true :=
      (Theta.acceptedCode_iff r _).mpr
        ⟨by simpa only [checkCode_code] using hnode.1, by simpa only [ThetaCourse.rawTree_code] using hnode.2.1⟩
    have hEq : equalCode r e (.theta m a : RelativeTerm Nat).code = true :=
      (equalCode_exact r e _).mpr
        ⟨((SourceDecomposition.inputCheck_exact r e).mp he).1, ((SourceDecomposition.inputCheck_exact r e).mp he).2,
          ((Theta.acceptedCode_iff r _).mp hsCode).1, ((Theta.acceptedCode_iff r _).mp hsCode).2,
          by simpa only [interpretation_code] using hsv.symm⟩
    have hLt : lessCode r d (SourceDecomposition.highCode r m a.code) = true :=
      (lessCode_exact r d _).mpr
        ⟨((SourceDecomposition.inputCheck_exact r d).mp hd).1, ((SourceDecomposition.inputCheck_exact r d).mp hd).2,
          ((Theta.acceptedCode_iff r _).mp hparts.1).1, ((Theta.acceptedCode_iff r _).mp hparts.1).2,
          by simpa only [checkedOrdinal_val, hhigh] using hΔΓ⟩
    exact ⟨.theta m a, hs, by simp only [nodeCandidate, beq_self_eq_true, hEq, hLt, Bool.true_and]⟩

theorem higherCheck_exact (r m d e : Nat) (hd : SourceDecomposition.inputCheck r d = true)
    (he : SourceDecomposition.inputCheck r e = true)
    (hηlow : interpretation r e < omegaSequence (finiteBase r) (m + 1)) :
    higherCheck r m d e = true ↔ SourceFixedPointLimits.GlobalHigherPresentation (finiteBase r)
      (finiteBase_pos r) m
        (checkedOrdinal r m d hd) (interpretation r e) := by
  rw [higherCheck, Bool.and_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨hst, s, hs, hc⟩
    exact nodeCandidate_higher r m d e hd he s hs hc hst
  · exact higher_has_candidate r m d e hd he hηlow

def unitCheck (r m d e : Nat) : Bool :=
  (r == 0) && ((m == 0) && (zeroCheck r d && equalCode 0 e oneCode))

theorem unitCheck_primrec : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => unitCheck p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hr : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => p.1) := Primrec.fst
  have hm : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have he : Primrec (fun p : Nat × (Nat × (Nat × Nat)) => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp (Primrec.beq.comp hr (Primrec.const 0))
    (Primrec.and.comp (Primrec.beq.comp hm (Primrec.const 0))
      (Primrec.and.comp (zeroCheck_primrec.comp hr hd)
        (equalCode_primrec.comp ((Primrec.const 0).pair (he.pair (Primrec.const oneCode))))))

theorem unitCheck_exact (r m d e : Nat) (hd : SourceDecomposition.inputCheck r d = true)
    (he : SourceDecomposition.inputCheck r e = true) : unitCheck r m d e = true ↔
    interpretation r e = 1 ∧ m = 0 ∧ r = 0 ∧ interpretation r d = 0 := by
  constructor
  · intro h
    have hs : r = 0 ∧ m = 0 ∧ zeroCheck r d = true ∧ equalCode 0 e oneCode = true := by
      simpa only [unitCheck, Bool.and_eq_true, beq_iff_eq] using h
    obtain ⟨rfl, hm, hz, ho⟩ := hs
    have hv := ((equalCode_exact 0 e oneCode).mp ho).2.2.2.2
    rw [oneCode_value] at hv
    exact ⟨hv, hm, rfl, (zeroCheck_exact 0 d hd).mp hz⟩
  · rintro ⟨hv, rfl, rfl, hz⟩
    have hzero := (zeroCheck_exact 0 d hd).mpr hz
    have hoe := (Theta.acceptedCode_iff 0 oneCode).mp oneCode_accepted
    have hee := (SourceDecomposition.inputCheck_exact 0 e).mp he
    have hone : equalCode 0 e oneCode = true :=
      (equalCode_exact 0 e oneCode).mpr ⟨hee.1, hee.2, hoe.1, hoe.2, hv.trans oneCode_value.symm⟩
    simp only [unitCheck, beq_self_eq_true, hzero, hone, Bool.true_and]

def fixedCode (r m c : Nat) : Bool := inputCheck r m c &&
  (zeroCheck r (SourceDecomposition.lowCode r m c) ||
    (unitCheck r m (SourceDecomposition.highCode r m c) (SourceDecomposition.lowCode r m c) ||
      higherCheck r m (SourceDecomposition.highCode r m c) (SourceDecomposition.lowCode r m c)))

def strictCode (r m c : Nat) : Bool := inputCheck r m c && !fixedCode r m c

theorem fixedCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => fixedCode p.1 p.2.1 p.2.2) := by
  have hd := SourceDecomposition.highCode_primrec
  have he := SourceDecomposition.lowCode_primrec
  have hp := Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair (hd.pair he))
  exact Primrec.and.comp inputCheck_primrec (Primrec.or.comp (zeroCheck_primrec.comp Primrec.fst he)
    (Primrec.or.comp (unitCheck_primrec.comp hp) (higherCheck_primrec.comp hp)))

theorem strictCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => strictCode p.1 p.2.1 p.2.2) :=
  Primrec.and.comp inputCheck_primrec (Primrec.not.comp fixedCode_primrec)

noncomputable def delta (r m c : Nat) : Ordinal.{0} :=
  omegaSequence (finiteBase r) (m + 1) * (interpretation r c / omegaSequence (finiteBase r) (m + 1))

noncomputable def residual (r m c : Nat) : Ordinal.{0} := interpretation r c % omegaSequence (finiteBase r) (m + 1)

def SourceFixed (r m c : Nat) : Prop :=
  SourceFixedPointLimits.globalResidualImageSup (finiteBase r) m (delta r m c) (residual r m c) = residual r m c

def SourceStrict (r m c : Nat) : Prop :=
  residual r m c < SourceFixedPointLimits.globalResidualImageSup (finiteBase r) m (delta r m c) (residual r m c)

/-- The executing criterion retains both ordinary-supremum boundary clauses.
Base one is exactly public level zero; higher sufficiency derives equality
directly, without a supplied limit classifier. -/
theorem fixed_parts_iff (r m c : Nat) (hc : inputCheck r m c = true) :
    SourceFixed r m c ↔ interpretation r (SourceDecomposition.lowCode r m c) = 0 ∨
      (interpretation r (SourceDecomposition.lowCode r m c) = 1 ∧ m = 0 ∧ r = 0 ∧
        interpretation r (SourceDecomposition.highCode r m c) = 0) ∨
      SourceFixedPointLimits.GlobalHigherPresentation (finiteBase r)
        (finiteBase_pos r) m
        (checkedOrdinal r m (SourceDecomposition.highCode r m c) (SourceDecomposition.parts_accepted r m c (Bool.and_eq_true_iff.mp hc).1).1)
        (interpretation r (SourceDecomposition.lowCode r m c)) := by
  have hi := (Bool.and_eq_true_iff.mp hc).1
  have hs := (inputCheck_exact r m c).mp hc
  have hparts := SourceDecomposition.parts_accepted r m c hi
  let d := SourceDecomposition.highCode r m c
  let e := SourceDecomposition.lowCode r m c
  have hd : SourceDecomposition.inputCheck r d = true := hparts.1
  have he : SourceDecomposition.inputCheck r e = true := hparts.2
  let dn := checkedOrdinal r m d hd
  have hdSort : dn.val < omegaSequence (finiteBase r) (m + 2) := by
    rw [checkedOrdinal_val, (SourceDecomposition.parts_code_value r m c hi).1]
    exact (Ordinal.mul_div_le _ _).trans_lt hs.2.2
  have hddvd : omegaSequence (finiteBase r) (m + 1) ∣ dn.val := by
    rw [checkedOrdinal_val]
    exact SourceDecomposition.highPart_dvd r m c hi
  have heLow := SourceDecomposition.lowPart_bound r m c hi
  have harg : GlobalNotation (finiteBase r) m (dn.val + interpretation r e) := by
    rw [checkedOrdinal_val, SourceDecomposition.parts_reconstruct r m c hi]
    rw [SourceDecomposition.input_value r c hi]
    exact checked_notation_at r _ (SourceDecomposition.input_tree r c hi).1 m
  have hcriterion := SourceFixedPointLimits.global_source_argument_fixed_iff (finiteBase r) (finiteBase_pos r)
    m dn hdSort hddvd (interpretation r e) heLow harg
  have hvalue := SourceDecomposition.parts_code_value r m c hi
  change SourceFixed r m c ↔ interpretation r e = 0 ∨ _
  unfold SourceFixed delta residual
  rw [← hvalue.1, ← hvalue.2]
  rw [show interpretation r (SourceDecomposition.highCode r m c) = dn.val from
    (checkedOrdinal_val r m d hd).symm]
  constructor
  · intro hfixed
    rcases hcriterion.mp hfixed with hz | hb | ⟨hl, hp⟩
    · exact Or.inl hz
    · exact Or.inr (Or.inl ⟨hb.1, hb.2.1, (finiteBase_eq_one_iff r).mp hb.2.2.1, hb.2.2.2⟩)
    · exact Or.inr (Or.inr hp)
  · rintro (hz | hb | hp)
    · exact hcriterion.mpr (Or.inl hz)
    · exact hcriterion.mpr (Or.inr (Or.inl ⟨hb.1, hb.2.1, (finiteBase_eq_one_iff r).mpr hb.2.2.1, hb.2.2.2⟩))
    · exact SourceFixedPointLimits.global_higherPresentation_fixed (finiteBase r) (finiteBase_pos r)
        m dn hdSort hddvd (interpretation r e) heLow hp

theorem fixedCode_correct (r m c : Nat) (hc : inputCheck r m c = true) :
    fixedCode r m c = true ↔ SourceFixed r m c := by
  have hi := (Bool.and_eq_true_iff.mp hc).1
  have hparts := SourceDecomposition.parts_accepted r m c hi
  rw [fixedCode, hc, Bool.true_and, Bool.or_eq_true,
    zeroCheck_exact r _ hparts.2,
    Bool.or_eq_true, unitCheck_exact r m _ _ hparts.1 hparts.2,
    higherCheck_exact r m _ _ hparts.1 hparts.2 (SourceDecomposition.lowPart_bound r m c hi)]
  exact (fixed_parts_iff r m c hc).symm

theorem strictCode_correct (r m c : Nat) (hc : inputCheck r m c = true) :
    strictCode r m c = true ↔ SourceStrict r m c := by
  have hi := (Bool.and_eq_true_iff.mp hc).1
  have hs := (inputCheck_exact r m c).mp hc
  have hparts := SourceDecomposition.parts_accepted r m c hi
  have hd : SourceDecomposition.inputCheck r (SourceDecomposition.highCode r m c) = true := hparts.1
  let dn := checkedOrdinal r m (SourceDecomposition.highCode r m c) hd
  have hdSort : dn.val < omegaSequence (finiteBase r) (m + 2) := by
    rw [checkedOrdinal_val, (SourceDecomposition.parts_code_value r m c hi).1]
    exact (Ordinal.mul_div_le _ _).trans_lt hs.2.2
  have hddvd : omegaSequence (finiteBase r) (m + 1) ∣ dn.val := by
    rw [checkedOrdinal_val]
    exact SourceDecomposition.highPart_dvd r m c hi
  have heLow := SourceDecomposition.lowPart_bound r m c hi
  have hstrict := SourceFixedPointLimits.global_strict_sup_iff_not_fixed (finiteBase r) (finiteBase_pos r)
    m dn hdSort hddvd (interpretation r (SourceDecomposition.lowCode r m c)) heLow
  rw [checkedOrdinal_val, (SourceDecomposition.parts_code_value r m c hi).1,
    (SourceDecomposition.parts_code_value r m c hi).2] at hstrict
  have hb : ((!fixedCode r m c) = true) ↔ ¬ (fixedCode r m c = true) := by
    cases fixedCode r m c <;> decide
  rw [strictCode, hc, Bool.true_and, hb, fixedCode_correct r m c hc]
  exact hstrict.symm

theorem fixedCode_exact (r m c : Nat) : fixedCode r m c = true ↔
    inputCheck r m c = true ∧ SourceFixed r m c := by
  constructor
  · intro h
    have hc := (Bool.and_eq_true_iff.mp h).1
    exact ⟨hc, (fixedCode_correct r m c hc).mp h⟩
  · rintro ⟨hc, hp⟩
    exact (fixedCode_correct r m c hc).mpr hp

theorem strictCode_exact (r m c : Nat) : strictCode r m c = true ↔
    inputCheck r m c = true ∧ SourceStrict r m c := by
  constructor
  · intro h
    have hc := (Bool.and_eq_true_iff.mp h).1
    exact ⟨hc, (strictCode_correct r m c hc).mp h⟩
  · rintro ⟨hc, hp⟩
    exact (strictCode_correct r m c hc).mpr hp

/-- The raw domain admits every original public term with the actual source
argument sort. Weak normality is constructed by genuine normalization. -/
def rawInputCheck (r m c : Nat) : Bool := checkCode r c && decide ((ThetaCourse.rawTree c).outerSort ≤ m + 2)

theorem rawInputCheck_primrec : Primrec (fun p : Nat × (Nat × Nat) => rawInputCheck p.1 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : Nat × (Nat × Nat) => checkCode p.1 p.2.2) :=
    Uniform.hereditaryCheckCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun p : Nat × (Nat × Nat) => (ThetaCourse.rawTree p.2.2).outerSort) :=
    outerSort_primrec.comp (ThetaCourse.rawTree_primrec.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.and.comp hc ((Primrec.nat_le.comp hs
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2))).decide)

theorem rawInputCheck_exact (r m c : Nat) : rawInputCheck r m c = true ↔
    checkCode r c = true ∧ interpretation r c < omegaSequence (finiteBase r) (m + 2) := by
  simp only [rawInputCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hs⟩
    obtain ⟨t, ht, hct⟩ := (checkCode_iff r c).mp hc
    exact ⟨hc, by simpa only [← ht, interpretation_code, ThetaCourse.rawTree_code] using
      ((denote_lt_iff_outerSort_le r t hct (m + 2) (by omega)).mpr
        (by simpa only [← ht, ThetaCourse.rawTree_code] using hs))⟩
  · rintro ⟨hc, hs⟩
    obtain ⟨t, ht, hct⟩ := (checkCode_iff r c).mp hc
    exact ⟨hc, by simpa only [← ht, ThetaCourse.rawTree_code] using
      ((denote_lt_iff_outerSort_le r t hct (m + 2) (by omega)).mp
        (by simpa only [← ht, interpretation_code] using hs))⟩

theorem normalized_input (r m c : Nat) (hc : rawInputCheck r m c = true) :
    inputCheck r m (Theta.Normalization.normalizeCode r c) = true := by
  have hs := (rawInputCheck_exact r m c).mp hc
  have hn := Theta.Normalization.normalizeCode_checked r c hs.1
  exact (inputCheck_exact r m _).mpr ⟨hn.1, hn.2.1, hn.2.2.trans_lt hs.2⟩

def fixedRawCode (r m c : Nat) : Bool := rawInputCheck r m c && fixedCode r m (Theta.Normalization.normalizeCode r c)

def strictRawCode (r m c : Nat) : Bool := rawInputCheck r m c && strictCode r m (Theta.Normalization.normalizeCode r c)

theorem fixedRawCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => fixedRawCode p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : Nat × (Nat × Nat) => Theta.Normalization.normalizeCode p.1 p.2.2) := Theta.Normalization.Effective.normalizeCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp rawInputCheck_primrec
    (fixedCode_primrec.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair hn)))

theorem strictRawCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => strictRawCode p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : Nat × (Nat × Nat) => Theta.Normalization.normalizeCode p.1 p.2.2) := Theta.Normalization.Effective.normalizeCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp rawInputCheck_primrec
    (strictCode_primrec.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair hn)))

theorem fixedRawCode_exact (r m c : Nat) : fixedRawCode r m c = true ↔
    checkCode r c = true ∧ interpretation r c < omegaSequence (finiteBase r) (m + 2) ∧ SourceFixed r m c := by
  constructor
  · intro h
    obtain ⟨hc, hf⟩ := Bool.and_eq_true_iff.mp h
    have hs := (rawInputCheck_exact r m c).mp hc
    have hn := Theta.Normalization.normalizeCode_checked r c hs.1
    have hp := (fixedCode_correct r m _ (normalized_input r m c hc)).mp hf
    rw [SourceFixed, delta, residual, hn.2.2] at hp
    exact ⟨hs.1, hs.2, hp⟩
  · rintro ⟨hc, hs, hp⟩
    have hi := (rawInputCheck_exact r m c).mpr ⟨hc, hs⟩
    have hn := Theta.Normalization.normalizeCode_checked r c hc
    apply Bool.and_eq_true_iff.mpr
    refine ⟨hi, (fixedCode_correct r m _ (normalized_input r m c hi)).mpr ?_⟩
    unfold SourceFixed delta residual
    rw [hn.2.2]
    exact hp

theorem strictRawCode_exact (r m c : Nat) : strictRawCode r m c = true ↔
    checkCode r c = true ∧ interpretation r c < omegaSequence (finiteBase r) (m + 2) ∧ SourceStrict r m c := by
  constructor
  · intro h
    obtain ⟨hc, hf⟩ := Bool.and_eq_true_iff.mp h
    have hs := (rawInputCheck_exact r m c).mp hc
    have hn := Theta.Normalization.normalizeCode_checked r c hs.1
    have hp := (strictCode_correct r m _ (normalized_input r m c hc)).mp hf
    rw [SourceStrict, delta, residual, hn.2.2] at hp
    exact ⟨hs.1, hs.2, hp⟩
  · rintro ⟨hc, hs, hp⟩
    have hi := (rawInputCheck_exact r m c).mpr ⟨hc, hs⟩
    have hn := Theta.Normalization.normalizeCode_checked r c hc
    apply Bool.and_eq_true_iff.mpr
    refine ⟨hi, (strictCode_correct r m _ (normalized_input r m c hi)).mpr ?_⟩
    unfold SourceStrict delta residual
    rw [hn.2.2]
    exact hp

private theorem strictRawCode_false_of_fixed (r m c : Nat) (hf : fixedRawCode r m c = true) :
    strictRawCode r m c = false := by
  have hn := (Bool.and_eq_true_iff.mp hf).2
  simp [strictRawCode, strictCode, hn]

/-- Empty residual images are fixed, and the literal strict test rejects
them on the entire original raw admitted sorted domain. -/
theorem fixedRawCode_zero_residual (r m c : Nat) (hc : checkCode r c = true)
    (hs : interpretation r c < omegaSequence (finiteBase r) (m + 2))
    (hz : residual r m c = 0) : fixedRawCode r m c = true ∧ strictRawCode r m c = false := by
  have he : SourceFixed r m c := by
    unfold SourceFixed
    rw [hz, SourceFixedPointLimits.globalResidualImageSup, Ordinal.bsup_zero]
  have hf := (fixedRawCode_exact r m c).mpr ⟨hc, hs, he⟩
  exact ⟨hf, strictRawCode_false_of_fixed r m c hf⟩

/-- The unique nonzero successor boundary also remains fixed and is
rejected by strict comparison, including non-normal original spellings. -/
theorem fixedRawCode_unit_boundary (r m c : Nat) (hc : checkCode r c = true)
    (hs : interpretation r c < omegaSequence (finiteBase r) (m + 2))
    (hr : r = 0) (hm : m = 0) (hd : delta r m c = 0) (he : residual r m c = 1) :
    fixedRawCode r m c = true ∧ strictRawCode r m c = false := by
  subst r
  subst m
  have hb : SourceFixed 0 0 c := by
    unfold SourceFixed
    rw [hd, he, finiteBase_zero, SourceFixedPointLimits.globalResidualImageSup,
      Ordinal.bsup_one, zero_add]
    simpa only [omegaSequence_zero] using
      globalCollapse_zero 1 zero_lt_one Ordinal.isPrincipal_add_one 0
  have hf := (fixedRawCode_exact 0 0 c).mpr ⟨hc, hs, hb⟩
  exact ⟨hf, strictRawCode_false_of_fixed 0 0 c hf⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceFixedPoint
