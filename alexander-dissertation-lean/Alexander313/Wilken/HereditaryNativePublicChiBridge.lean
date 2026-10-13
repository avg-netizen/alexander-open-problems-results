import Alexander313.Wilken.HereditaryNativePublicBridge

/-!
# The genuine public-to-native indicator bridge at one and the same epsilon

The original public level s+1 and the native contextCode s have the same
actual epsilon base. Their atomic parameter ANF spellings can differ. A joint
induction compares the indicator and the finite retained high-label Boolean
stream instead: every parameter head is below the high cut, and each retained
theta is the actual translated literal node. Actual denotation and divmod
agreement identify the fixed-supremum/logend-zero branch tests.

This proves Definition3.3 indicator agreement for the checked original public
normal tree and its real mapParameters image. The raw operation first builds
the public normal tree and then translates it. It does not identify separately
run native/public normalizers, prove arbitrary-spelling invariance, or prove
the different-base source translation in Lemma3.4. All terms are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativePublicBridge

theorem baseCase_agreement (s m : Nat) (a : RelativeTerm Nat)
    (ht : check (s + 1) (.theta m a) = true) (hn : Theta.Normal (s + 1) (.theta m a)) :
    NativeContext.SourceChi.baseCase (contextCode s) m (translate s a).code =
      SourceChi.baseCase (s + 1) m a.code := by
  have hp := (SourceChi.theta_argument_parts (s + 1) m a ht hn).1
  have hnp := translateCode_accepted s a.code hp
  apply Bool.eq_iff_iff.mpr
  simp only [NativeContext.SourceChi.baseCase, SourceChi.baseCase, Bool.and_eq_true]
  rw [NativeContext.FixedPoint.zeroCheck_exact (contextCode s) _
      (by simpa only [translateCode_code] using hnp), SourceFixedPoint.zeroCheck_exact _ _ hp]
  simp only [NativeContext.interpretation_code, interpretation_code, translate_denote]

theorem chooseHigh_agreement (s m : Nat) (a : RelativeTerm Nat)
    (ht : check (s + 1) (.theta m a) = true) (hn : Theta.Normal (s + 1) (.theta m a)) :
    NativeContext.SourceChi.chooseHigh (contextCode s) m (translate s a).code =
      SourceChi.chooseHigh (s + 1) m a.code := by
  have hnt : NativeContext.check (contextCode s) (.theta m (translate s a)) = true :=
    (translate_check s (.theta m a)).trans ht
  have hnn : NativeContext.Comparison.Normal (contextCode s) (.theta m (translate s a)) :=
    by simpa only [translate_theta] using translate_normal s (.theta m a) hn
  have hp := (SourceChi.theta_argument_parts (s + 1) m a ht hn).1
  have hv := parts_values s m a.code hp
  apply Bool.eq_iff_iff.mpr
  rw [NativeContext.SourceChi.chooseHigh_correct _ _ _ hnt hnn,
    SourceChi.chooseHigh_correct _ _ _ ht hn]
  have hf : NativeContext.FixedPoint.SourceFixed (contextCode s) m (translate s a).code ↔
      SourceFixedPoint.SourceFixed (s + 1) m a.code := by
    simp only [NativeContext.FixedPoint.SourceFixed, NativeContext.FixedPoint.delta,
    NativeContext.FixedPoint.residual, SourceFixedPoint.SourceFixed, SourceFixedPoint.delta,
    SourceFixedPoint.residual, contextCode_value, NativeContext.interpretation_code,
      interpretation_code, translate_denote]
  have hl : NativeContext.interpretation (contextCode s)
      (NativeContext.Decomposition.lowCode m (translate s a).code) =
      interpretation (s + 1) (SourceDecomposition.lowCode (s + 1) m a.code) := by
    simpa only [translateCode_code] using hv.2
  exact or_congr hf (congrArg LogEndZero.SourceZero hl).to_iff

private theorem highLabels_same (m : Nat) (es : List SourceChi.Entry) :
    NativeContext.SourceChi.highLabels m es = SourceChi.highLabels m es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [NativeContext.SourceChi.highLabels, SourceChi.highLabels, ih,
      NativeContext.Decomposition.above, SourceDecomposition.above]

private theorem highLabels_append (m : Nat) (as bs : List SourceChi.Entry) :
    SourceChi.highLabels m (as ++ bs) = SourceChi.highLabels m as ++ SourceChi.highLabels m bs := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases h : SourceDecomposition.above m a.1 <;>
      simp only [List.cons_append, SourceChi.highLabels, h, Bool.cond_false, Bool.cond_true, ih]

private theorem parameter_atoms_shape (s p : Nat) (a : RelativeTerm Nat)
    (ha : a ∈ Theta.atoms (s + 1) (.parameter p)) : ∃ v, a = .parameter v := by
  change a ∈ ((decode p).map (fun u =>
    (Theta.atoms s u).map (fun b => RelativeTerm.parameter b.code))).getD [] at ha
  cases hd : decode p with
  | none => simp only [hd, Option.map_none, Option.getD_none, List.not_mem_nil] at ha
  | some u =>
    simp only [hd, Option.map_some, Option.getD_some] at ha
    obtain ⟨b, hb, he⟩ := List.mem_map.mp ha
    exact ⟨b.code, he.symm⟩

private theorem highLabels_parameters (m : Nat) (es : List SourceChi.Entry)
    (he : ∀ e ∈ es, ∃ p, e.1 = .parameter p) : SourceChi.highLabels m es = [] := by
  revert he
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
    intro he
    obtain ⟨p, hp⟩ := he e (List.mem_cons_self ..)
    have hc : SourceDecomposition.above m e.1 = false := by
      rw [hp]
      simp [SourceDecomposition.above, outerSort]
    simp only [SourceChi.highLabels, hc, Bool.cond_false]
    exact ih (fun d hd => he d (List.mem_cons_of_mem _ hd))

private def publicHighBits (s m : Nat) (t : RelativeTerm Nat) : List Bool :=
  (SourceChi.highLabels m (SourceChi.state (s + 1) t).2.2).map Prod.snd

private def nativeHighBits (s m : Nat) (t : RelativeTerm Nat) : List Bool :=
  (NativeContext.SourceChi.highLabels m (NativeContext.SourceChi.state (contextCode s) t).2.2).map Prod.snd

private theorem publicHighBits_parameter (s m p : Nat) : publicHighBits s m (.parameter p) = [] := by
  unfold publicHighBits
  rw [SourceChi.state_labels]
  have h := highLabels_parameters m ((Theta.atoms (s + 1) (.parameter p)).map
    (fun a => (a, SourceChi.indicator (s + 1) a))) (by
      intro e he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      exact parameter_atoms_shape s p a ha)
  rw [h]
  rfl

private theorem nativeHighBits_parameter (s m p : Nat) : nativeHighBits s m (.parameter p) = [] := by
  unfold nativeHighBits
  rw [highLabels_same, NativeContext.SourceChi.state_labels]
  have h := highLabels_parameters m ((NativeContext.Comparison.atoms (.parameter p)).map
    (fun a => (a, NativeContext.SourceChi.indicator (contextCode s) a))) (by
      intro e he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      obtain ⟨v, hv, he⟩ := List.mem_map.mp ha
      exact ⟨v, he.symm⟩)
  rw [h]
  rfl

private theorem publicHighBits_sum (s m : Nat) (a b : RelativeTerm Nat) :
    publicHighBits s m (.sum a b) = publicHighBits s m a ++ publicHighBits s m b := by
  change (SourceChi.highLabels m ((SourceChi.state (s + 1) a).2.2 ++
    (SourceChi.state (s + 1) b).2.2)).map Prod.snd = _
  rw [highLabels_append, List.map_append]
  rfl

private theorem nativeHighBits_sum (s m : Nat) (a b : RelativeTerm Nat) :
    nativeHighBits s m (.sum a b) = nativeHighBits s m a ++ nativeHighBits s m b := by
  change (NativeContext.SourceChi.highLabels m ((NativeContext.SourceChi.state (contextCode s) a).2.2 ++
    (NativeContext.SourceChi.state (contextCode s) b).2.2)).map Prod.snd = _
  simp only [nativeHighBits, highLabels_same, highLabels_append, List.map_append]

private theorem publicHighBits_theta (s m k : Nat) (a : RelativeTerm Nat) :
    publicHighBits s m (.theta k a) =
      if m < k then [SourceChi.indicator (s + 1) (.theta k a)] else [] := by
  change (SourceChi.highLabels m [(.theta k (SourceChi.state (s + 1) a).1,
    SourceChi.indicator (s + 1) (.theta k a))]).map Prod.snd = _
  rw [SourceChi.state_tree]
  by_cases h : m < k
  · have hh : m + 1 < k + 1 := by omega
    simp only [SourceChi.highLabels, SourceDecomposition.above, outerSort, hh, decide_true,
      Bool.cond_true, List.map_cons, List.map_nil, if_pos h]
  · have hh : ¬m + 1 < k + 1 := by omega
    simp only [SourceChi.highLabels, SourceDecomposition.above, outerSort, hh, decide_false,
      Bool.cond_false, List.map_nil, if_neg h]

private theorem nativeHighBits_theta (s m k : Nat) (a : RelativeTerm Nat) :
    nativeHighBits s m (.theta k a) =
      if m < k then [NativeContext.SourceChi.indicator (contextCode s) (.theta k a)] else [] := by
  change (NativeContext.SourceChi.highLabels m [(.theta k (NativeContext.SourceChi.state (contextCode s) a).1,
    NativeContext.SourceChi.indicator (contextCode s) (.theta k a))]).map Prod.snd = _
  rw [NativeContext.SourceChi.state_tree, highLabels_same]
  by_cases h : m < k
  · have hh : m + 1 < k + 1 := by omega
    simp only [SourceChi.highLabels, SourceDecomposition.above, outerSort, hh, decide_true,
      Bool.cond_true, List.map_cons, List.map_nil, if_pos h]
  · have hh : ¬m + 1 < k + 1 := by omega
    simp only [SourceChi.highLabels, SourceDecomposition.above, outerSort, hh, decide_false,
      Bool.cond_false, List.map_nil, if_neg h]

private theorem lastIndicator_bits (es : List SourceChi.Entry) :
    SourceChi.lastIndicator es = (es.map Prod.snd).reverse.head?.getD false := by
  unfold SourceChi.lastIndicator
  rw [← List.map_reverse]
  cases hr : es.reverse with
  | nil => rfl
  | cons e es => rfl

private theorem public_indicator_theta_labels (r m : Nat) (a : RelativeTerm Nat) :
    SourceChi.indicator r (.theta m a) = cond (SourceChi.baseCase r m a.code) true
      (cond (SourceChi.chooseHigh r m a.code)
        (SourceChi.lastIndicator (SourceChi.highLabels m (SourceChi.state r a).2.2))
        (SourceChi.indicator r a)) := by
  change cond (SourceChi.baseCase r m (SourceChi.state r a).1.code) true
    (cond (SourceChi.chooseHigh r m (SourceChi.state r a).1.code) _ _) = _
  rw [SourceChi.state_tree]

private theorem native_indicator_theta_labels (q m : Nat) (a : RelativeTerm Nat) :
    NativeContext.SourceChi.indicator q (.theta m a) = cond (NativeContext.SourceChi.baseCase q m a.code) true
      (cond (NativeContext.SourceChi.chooseHigh q m a.code)
        (NativeContext.SourceChi.lastIndicator (NativeContext.SourceChi.highLabels m
          (NativeContext.SourceChi.state q a).2.2)) (NativeContext.SourceChi.indicator q a)) := by
  change cond (NativeContext.SourceChi.baseCase q m (NativeContext.SourceChi.state q a).1.code) true
    (cond (NativeContext.SourceChi.chooseHigh q m (NativeContext.SourceChi.state q a).1.code) _ _) = _
  rw [NativeContext.SourceChi.state_tree]

private theorem indicator_and_highBits (s : Nat) (t : RelativeTerm Nat)
    (ht : check (s + 1) t = true) (hn : Theta.Normal (s + 1) t) :
    NativeContext.SourceChi.indicator (contextCode s) (translate s t) = SourceChi.indicator (s + 1) t ∧
      ∀ m, nativeHighBits s m (translate s t) = publicHighBits s m t := by
  revert ht hn
  induction t with
  | parameter p =>
    intro ht hn
    refine ⟨rfl, ?_⟩
    intro m
    rw [translate_parameter, nativeHighBits_parameter, publicHighBits_parameter]
  | sum a b iha ihb =>
    intro ht hn
    have hs := SourceChi.sum_children (s + 1) a b ht hn
    have ha := iha hs.1 hs.2.1
    have hb := ihb hs.2.2.1 hs.2.2.2.1
    refine ⟨?_, ?_⟩
    · simpa only [translate_sum, NativeContext.SourceChi.indicator_sum, SourceChi.indicator_sum] using hb.1
    · intro m
      rw [translate_sum, nativeHighBits_sum, publicHighBits_sum, ha.2 m, hb.2 m]
  | theta k a ih =>
    intro ht hn
    have ha := ih (SourceFixedPoint.checked_theta_argument (s + 1) k a ht)
      ((Theta.normal_theta (s + 1) k a).mp hn)
    have hlast : NativeContext.SourceChi.lastIndicator
        (NativeContext.SourceChi.highLabels k (NativeContext.SourceChi.state (contextCode s) (translate s a)).2.2) =
      SourceChi.lastIndicator (SourceChi.highLabels k (SourceChi.state (s + 1) a).2.2) := by
      change SourceChi.lastIndicator _ = _
      rw [lastIndicator_bits, lastIndicator_bits]
      exact congrArg (fun bs : List Bool => bs.reverse.head?.getD false) (ha.2 k)
    have hi : NativeContext.SourceChi.indicator (contextCode s) (translate s (.theta k a)) =
        SourceChi.indicator (s + 1) (.theta k a) := by
      rw [translate_theta, native_indicator_theta_labels, public_indicator_theta_labels,
        baseCase_agreement s k a ht hn, chooseHigh_agreement s k a ht hn, hlast, ha.1]
    refine ⟨hi, ?_⟩
    intro m
    simpa only [translate_theta, nativeHighBits_theta, publicHighBits_theta] using
      congrArg (fun b : Bool => if m < k then [b] else []) hi

theorem indicator_agreement (s : Nat) (t : RelativeTerm Nat)
    (ht : check (s + 1) t = true) (hn : Theta.Normal (s + 1) t) :
    NativeContext.SourceChi.indicator (contextCode s) (translate s t) = SourceChi.indicator (s + 1) t :=
  (indicator_and_highBits s t ht hn).1

theorem chiCode_agreement (s c : Nat) (hc : SourceDecomposition.inputCheck (s + 1) c = true) :
    NativeContext.SourceChi.chiCode (contextCode s) (translateCode s c) = SourceChi.chiCode (s + 1) c := by
  have hs := (SourceDecomposition.inputCheck_exact (s + 1) c).mp hc
  obtain ⟨t, rfl, ht⟩ := (checkCode_iff (s + 1) c).mp hs.1
  have hn : Theta.Normal (s + 1) t := by simpa only [ThetaCourse.rawTree_code] using hs.2
  rw [translateCode_code, NativeContext.SourceChi.chiCode_correct _ _
    (by simpa only [translate_check] using ht) (translate_normal s t hn),
    SourceChi.chiCode_correct _ _ (Nat.succ_pos s) ht hn]
  exact indicator_agreement s t ht hn

theorem dualCode_agreement (s c : Nat) (hc : SourceDecomposition.inputCheck (s + 1) c = true) :
    NativeContext.SourceChi.dualCode (contextCode s) (translateCode s c) = SourceChi.dualCode (s + 1) c := by
  have hs := (SourceDecomposition.inputCheck_exact (s + 1) c).mp hc
  obtain ⟨t, rfl, ht⟩ := (checkCode_iff (s + 1) c).mp hs.1
  have hn : Theta.Normal (s + 1) t := by simpa only [ThetaCourse.rawTree_code] using hs.2
  rw [translateCode_code, NativeContext.SourceChi.dualCode_correct _ _
    (by simpa only [translate_check] using ht) (translate_normal s t hn),
    SourceChi.dualCode_correct _ _ (Nat.succ_pos s) ht hn, indicator_agreement s t ht hn]

/-- Full-original raw input: use the actual publicly constructed normal
spelling, then execute native chi on its translated tree. -/
def translatedRawChi (s c : Nat) : Bool := checkCode (s + 1) c &&
  NativeContext.SourceChi.chiCode (contextCode s) (normalizedCode s c)

theorem translatedRawChi_primrec : Primrec₂ translatedRawChi := by
  have hg := Uniform.hereditaryCheckCode_primrec.comp (Primrec.succ.comp Primrec.fst) Primrec.snd
  have hv := NativeContext.SourceChi.chiCode_primrec.comp (contextCode_primrec.comp Primrec.fst)
    normalizedCode_primrec
  exact (Primrec.and.comp hg hv).to₂

theorem translatedRawChi_agreement (s c : Nat) : translatedRawChi s c = SourceChi.rawChiCode (s + 1) c := by
  by_cases hc : checkCode (s + 1) c = true
  · have hn := Theta.Normalization.normalizeCode_accepted (s + 1) c hc
    have hv := chiCode_agreement s _ hn.1
    simpa only [translatedRawChi, normalizedCode, SourceChi.rawChiCode, SourceChi.rawInputCheck,
      Nat.succ_pos, decide_true, hc, Bool.true_and] using hv
  · have hf : checkCode (s + 1) c = false := by cases h : checkCode (s + 1) c <;> simp_all
    simp only [translatedRawChi, SourceChi.rawChiCode, SourceChi.rawInputCheck,
      Nat.succ_pos, decide_true, hf, Bool.true_and, Bool.false_and]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativePublicBridge
