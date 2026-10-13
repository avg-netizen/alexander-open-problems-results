import Alexander313.Wilken.PublicEpsilonNativeIotaFixedPointTransportSupport
import Alexander313.Wilken.HereditaryNativeSourceChiInvariance

/-!
# Genuine shifted higher-presentation tests

Checked principal representatives are compared through their actual ordinal
values. The source mapped principal word and target canonical ANF supply the
alignment; no literal equality of newly created parameter words is assumed.
The source and target indicator bases remain distinct. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.FixedPointTransport

open ThetaCourse

private theorem equalCode_iff (q : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true)
    (hnt : Comparison.Normal q t) (hnu : Comparison.Normal q u) :
    Comparison.equalCode q t.code u.code = true ↔ denote q t = denote q u := by
  constructor
  · intro h
    have hv := ((Comparison.equalCode_exact q _ _).mp h).2.2.2.2
    simpa only [interpretation_code] using hv
  · intro h
    apply (Comparison.equalCode_exact q _ _).mpr
    exact ⟨by simpa only [checkCode_code] using ht,
      by simpa only [rawTree_code] using hnt,
      by simpa only [checkCode_code] using hu,
      by simpa only [rawTree_code] using hnu,
      by simpa only [interpretation_code] using h⟩

private theorem lessCode_iff (q : Nat) (t u : RelativeTerm Nat)
    (ht : check q t = true) (hu : check q u = true)
    (hnt : Comparison.Normal q t) (hnu : Comparison.Normal q u) :
    Comparison.lessCode q t.code u.code = true ↔ denote q t < denote q u := by
  constructor
  · intro h
    have hv := ((Comparison.lessCode_exact q _ _).mp h).2.2.2.2
    simpa only [interpretation_code] using hv
  · intro h
    apply (Comparison.lessCode_exact q _ _).mpr
    exact ⟨by simpa only [checkCode_code] using ht,
      by simpa only [rawTree_code] using hnt,
      by simpa only [checkCode_code] using hu,
      by simpa only [rawTree_code] using hnu,
      by simpa only [interpretation_code] using h⟩

private theorem nodeCandidate_theta_iff (q m : Nat) (d e : RelativeTerm Nat)
    (k : Nat) (a : RelativeTerm Nat)
    (hd : check q d = true) (he : check q e = true)
    (hnd : Comparison.Normal q d) (hne : Comparison.Normal q e)
    (ha : check q (.theta k a) = true) (hna : Comparison.Normal q (.theta k a)) :
    FixedPoint.nodeCandidate q m d.code e.code (.theta k a) = true ↔
      k = m ∧ denote q e = denote q (.theta k a) ∧
        denote q d < denote q (Decomposition.highPartTerm m a.code) := by
  have hac := FixedPoint.checked_theta_argument q k a ha
  have hai := ReturnedIota.original_accepted q a hac hna
  have hp := (Decomposition.parts_checked q m a.code hai).1
  have hnp := (Decomposition.parts_normal q m a.code hai).1
  simp only [FixedPoint.nodeCandidate, Bool.and_eq_true, beq_iff_eq,
    equalCode_iff q e (.theta k a) he ha hne hna, Decomposition.highCode,
    lessCode_iff q d (Decomposition.highPartTerm m a.code) hd hp hnd hnp]

/-- Actual higher-candidate flags are invariant between checked principal
node representatives at the SAME base and ordinal value. -/
theorem nodeCandidate_value_invariant (q m : Nat) (d e s t : RelativeTerm Nat)
    (hd : check q d = true) (he : check q e = true)
    (hnd : Comparison.Normal q d) (hne : Comparison.Normal q e)
    (hs : check q s = true) (ht : check q t = true)
    (hns : Comparison.Normal q s) (hnt : Comparison.Normal q t)
    (hss : (∃ p, s = .parameter p) ∨ ∃ k a, s = .theta k a)
    (hst : (∃ p, t = .parameter p) ∨ ∃ k a, t = .theta k a)
    (hv : denote q s = denote q t) :
    FixedPoint.nodeCandidate q m d.code e.code s =
      FixedPoint.nodeCandidate q m d.code e.code t := by
  rcases hss with ⟨p, rfl⟩ | ⟨k, a, rfl⟩
  · rcases hst with ⟨p', rfl⟩ | ⟨l, a', rfl⟩
    · rfl
    · have hb := FixedPoint.checked_parameter_lt_base q p hs
      have hr := (FixedPoint.checked_theta_range q l a' ht).1
      have hbase : base q ≤ denote q (.theta l a') :=
        ((omegaSequence_strictMono (base q)).monotone (Nat.zero_le l)).trans hr
      exact False.elim (hb.not_ge (hbase.trans_eq hv.symm))
  · rcases hst with ⟨p, rfl⟩ | ⟨l, a', rfl⟩
    · have hb := FixedPoint.checked_parameter_lt_base q p ht
      have hr := (FixedPoint.checked_theta_range q k a hs).1
      have hbase : base q ≤ denote q (.theta k a) :=
        ((omegaSequence_strictMono (base q)).monotone (Nat.zero_le k)).trans hr
      exact False.elim (hb.not_ge (hbase.trans_eq hv))
    · have hh := SourceChi.Invariance.theta_value_injective q k l a a' hs ht hv
      obtain ⟨rfl, harg⟩ := hh
      have hai := ReturnedIota.original_accepted q a
        (FixedPoint.checked_theta_argument q k a hs) hns
      have hai' := ReturnedIota.original_accepted q a'
        (FixedPoint.checked_theta_argument q k a' ht) hnt
      have hhigh : denote q (Decomposition.highPartTerm m a.code) =
          denote q (Decomposition.highPartTerm m a'.code) := by
        have h1 := (Decomposition.parts_code_value q m a.code hai).1
        have h2 := (Decomposition.parts_code_value q m a'.code hai').1
        simp only [Decomposition.highCode, interpretation_code] at h1 h2
        exact h1.trans ((congrArg (fun v => omegaSequence (base q) (m + 1) *
          (v / omegaSequence (base q) (m + 1))) harg).trans h2.symm)
      apply Bool.eq_iff_iff.mpr
      rw [nodeCandidate_theta_iff q m d e k a hd he hnd hne hs hns,
        nodeCandidate_theta_iff q m d e k a' hd he hnd hne ht hnt,
        hv, hhigh]

/-- Every mapped actual source atom has a genuine target principal shape. -/
theorem mapped_atom_shape (q b : Nat) (ha : rootCheck q b = true)
    (t x : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t)
    (hx : x ∈ Comparison.atoms t) :
    (∃ p, transform q b x = .parameter p) ∨
      ∃ k a, transform q b x = .theta k a := by
  have hxc := (Iota.OrderInduction.atoms_checked_normal q t x ht hn hx).1
  have hxr := OrderSupport.restricted_atoms q b t x hr hx
  rcases Comparison.atoms_shape t x hx with ⟨p, rfl⟩ | ⟨k, a, rfl⟩
  · exact Or.inl ⟨parameterCode q (.parameter p), rfl⟩
  · cases k with
    | zero => exact Or.inl ⟨parameterCode q (.theta 0 a),
        OrderSupport.transform_low q b ha _ hxc hxr le_rfl⟩
    | succ k => exact Or.inr ⟨k, transform q b a,
        OrderSupport.transform_theta_succ q b k ha a hxc hxr⟩

/-- A genuine mapped original principal node has exactly the shifted
higher-candidate flag, including the stopped level-zero source nodes. -/
theorem nodeCandidate_transform (q b m : Nat) (ha : rootCheck q b = true)
    (d e s : RelativeTerm Nat) (hd : check q d = true) (he : check q e = true)
    (hnd : Comparison.Normal q d) (hne : Comparison.Normal q e)
    (hrd : Restricted q b d) (hre : Restricted q b e)
    (hs : check q s = true) (hns : Comparison.Normal q s) (hrs : Restricted q b s)
    (hshape : (∃ p, s = .parameter p) ∨ ∃ k a, s = .theta k a) :
    FixedPoint.nodeCandidate (betaCode q b) m (transform q b d).code
      (transform q b e).code (transform q b s) =
        FixedPoint.nodeCandidate q (m + 1) d.code e.code s := by
  rcases hshape with ⟨p, rfl⟩ | ⟨k, a, rfl⟩
  · simp only [transform, FixedPoint.nodeCandidate]
  · cases k with
    | zero =>
      rw [OrderSupport.transform_low q b ha (.theta 0 a) hs hrs le_rfl]
      simp [FixedPoint.nodeCandidate]
    | succ k =>
      have hac := FixedPoint.checked_theta_argument q (k + 1) a hs
      have har := (restricted_theta_succ q b k a).mp hrs
      have hai := ReturnedIota.original_accepted q a hac hns
      have hpc := (Decomposition.parts_checked q (m + 1) a.code hai).1
      have hpn := (Decomposition.parts_normal q (m + 1) a.code hai).1
      have hpr := (parts_restricted q b (m + 1) a har).1
      have hdc := transform_checked q b ha d hd hrd
      have hec := transform_checked q b ha e he hre
      have hdn := transform_normal q b ha d hd hnd hrd
      have hen := transform_normal q b ha e he hne hre
      have hsc : check (betaCode q b) (.theta k (transform q b a)) = true := by
        rw [← OrderSupport.transform_theta_succ q b k ha a hs hrs]
        exact transform_checked q b ha (.theta (k + 1) a) hs hrs
      have hsn : Comparison.Normal (betaCode q b) (.theta k (transform q b a)) := by
        rw [← OrderSupport.transform_theta_succ q b k ha a hs hrs]
        exact transform_normal q b ha (.theta (k + 1) a) hs hns hrs
      rw [OrderSupport.transform_theta_succ q b k ha a hs hrs]
      apply Bool.eq_iff_iff.mpr
      rw [nodeCandidate_theta_iff (betaCode q b) m (transform q b d)
          (transform q b e) k (transform q b a) hdc hec hdn hen hsc hsn,
        nodeCandidate_theta_iff q (m + 1) d e (k + 1) a hd he hnd hne hs hns,
        highPart_transform_value q b m ha a hac hns har,
        ← OrderSupport.transform_theta_succ q b k ha a hs hrs,
        transform_eq_iff q b ha e (.theta (k + 1) a) he hs hne hns hre hrs,
        transform_lt_iff q b ha d (Decomposition.highPartTerm (m + 1) a.code)
          hd hpc hnd hpn hrd hpr]
      simp only [Nat.add_left_inj]

private theorem aligned_any {α : Type} (as bs : List α)
    (v : α → Ordinal.{0}) (P : α → Bool) (hv : as.map v = bs.map v)
    (he : ∀ a ∈ as, ∀ b ∈ bs, v a = v b → P a = P b) : as.any P = bs.any P := by
  revert bs hv he
  induction as with
  | nil =>
    intro bs hv he
    have hb : bs = [] := List.map_eq_nil_iff.mp hv.symm
    subst bs
    rfl
  | cons a as ih =>
    intro bs hv he
    cases bs with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hv
    | cons b bs =>
      have hh := List.cons.inj hv
      have hab := he a List.mem_cons_self b List.mem_cons_self hh.1
      have htail := ih bs hh.2 (fun x hx y hy hxy => he x
        (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy)
      simp only [List.any_cons, hab, htail]

/-- The actual target ANF supplies the same higher-candidate existential
as the mapped original ANF. Canonical parameter expansions need not agree
literally; checked principal VALUE alignment suffices. -/
theorem candidateWord_transform (q b m : Nat) (ha : rootCheck q b = true)
    (d e : RelativeTerm Nat) (hd : check q d = true) (he : check q e = true)
    (hnd : Comparison.Normal q d) (hne : Comparison.Normal q e)
    (hrd : Restricted q b d) (hre : Restricted q b e) :
    (Decomposition.word (transform q b e).code).any
      (FixedPoint.nodeCandidate (betaCode q b) m (transform q b d).code
        (transform q b e).code) =
      (Decomposition.word e.code).any (FixedPoint.nodeCandidate q (m + 1) d.code e.code) := by
  have hdc := transform_checked q b ha d hd hrd
  have hec := transform_checked q b ha e he hre
  have hdn := transform_normal q b ha d hd hnd hrd
  have hen := transform_normal q b ha e he hne hre
  have hei := ReturnedIota.original_accepted (betaCode q b) (transform q b e) hec hen
  have halign : (Decomposition.word (transform q b e).code).map (denote (betaCode q b)) =
      ((Comparison.atoms e).map (transform q b)).map (denote (betaCode q b)) := by
    rw [(Decomposition.word_spec (betaCode q b) _ hei).2, List.map_map,
      transform_atoms_anf q b ha e he hne hre]
  have hh := aligned_any (Decomposition.word (transform q b e).code)
    ((Comparison.atoms e).map (transform q b)) (denote (betaCode q b))
    (FixedPoint.nodeCandidate (betaCode q b) m (transform q b d).code
      (transform q b e).code) halign (by
        intro x hx y hy hxy
        have hxc := (Decomposition.word_spec (betaCode q b) _ hei).1 x hx
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        have hzc := Iota.OrderInduction.atoms_checked_normal q e z he hne hz
        have hzr := OrderSupport.restricted_atoms q b e z hre hz
        exact nodeCandidate_value_invariant (betaCode q b) m
          (transform q b d) (transform q b e) x (transform q b z)
          hdc hec hdn hen hxc.1 (transform_checked q b ha z hzc.1 hzr)
          hxc.2.1 (transform_normal q b ha z hzc.1 hzc.2 hzr)
          (by apply Comparison.atoms_shape (transform q b e) x
              simpa only [Decomposition.word, rawTree_code] using hx)
          (mapped_atom_shape q b ha e z he hne hre hz) hxy)
  rw [hh, List.any_map]
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hP⟩
    have hxc := Iota.OrderInduction.atoms_checked_normal q e x he hne hx
    have hxr := OrderSupport.restricted_atoms q b e x hre hx
    refine ⟨x, by simpa only [Decomposition.word, rawTree_code] using hx, ?_⟩
    simpa only [Function.comp_apply, nodeCandidate_transform q b m ha d e x
      hd he hnd hne hrd hre hxc.1 hxc.2 hxr (Comparison.atoms_shape e x hx)] using hP
  · rintro ⟨x, hx, hP⟩
    have hx' : x ∈ Comparison.atoms e := by
      simpa only [Decomposition.word, rawTree_code] using hx
    have hxc := Iota.OrderInduction.atoms_checked_normal q e x he hne hx'
    have hxr := OrderSupport.restricted_atoms q b e x hre hx'
    refine ⟨x, hx', ?_⟩
    simpa only [Function.comp_apply, nodeCandidate_transform q b m ha d e x
      hd he hnd hne hrd hre hxc.1 hxc.2 hxr (Comparison.atoms_shape e x hx')] using hP

/-- The executing higher-presentation test shifts its actual level by one
on the genuine original checked Normal restricted pair. -/
theorem higherCheck_transform (q b m : Nat) (ha : rootCheck q b = true)
    (d e : RelativeTerm Nat) (hd : check q d = true) (he : check q e = true)
    (hnd : Comparison.Normal q d) (hne : Comparison.Normal q e)
    (hrd : Restricted q b d) (hre : Restricted q b e) :
    FixedPoint.higherCheck (betaCode q b) m (transform q b d).code
      (transform q b e).code = FixedPoint.higherCheck q (m + 1) d.code e.code := by
  rw [FixedPoint.higherCheck, FixedPoint.higherCheck,
    candidateWord_transform q b m ha d e hd he hnd hne hrd hre]
  simp only [FixedPoint.starCode, rawTree_code,
    starLess_transform q b m ha d e hd he hnd hne hrd hre]

/-- Within ONE base, the genuine semantic higher presentation depends on
its admitted high-part and residual values. This merely changes admitted
representatives; it is not a cross-base higher-presentation assumption. -/
theorem higherCheck_value_invariant (q m d e d' e' : Nat)
    (hd : Decomposition.inputCheck q d = true) (he : Decomposition.inputCheck q e = true)
    (hd' : Decomposition.inputCheck q d' = true) (he' : Decomposition.inputCheck q e' = true)
    (hη : interpretation q e < omegaSequence (base q) (m + 1))
    (hη' : interpretation q e' < omegaSequence (base q) (m + 1))
    (hv : interpretation q d = interpretation q d')
    (hw : interpretation q e = interpretation q e') :
    FixedPoint.higherCheck q m d e = FixedPoint.higherCheck q m d' e' := by
  have hΔ : FixedPoint.checkedOrdinal q m d hd = FixedPoint.checkedOrdinal q m d' hd' := by
    apply Subtype.ext
    simpa only [FixedPoint.checkedOrdinal_val] using hv
  apply Bool.eq_iff_iff.mpr
  rw [FixedPoint.higherCheck_exact q m d e hd he hη,
    FixedPoint.higherCheck_exact q m d' e' hd' he' hη', hΔ, hw]

theorem transform_zero_iff (q b : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) :
    denote (betaCode q b) (transform q b t) = 0 ↔ denote q t = 0 := by
  have hz := OrderSupport.transform_low_value q b ha Normalization.zeroTree
    (Normalization.zeroTree_checked q (source_checked q b ha))
    (OmegaQuotient.Support.zero_restricted q b) (Nat.zero_le 1)
  have he := transform_eq_iff q b ha t Normalization.zeroTree ht
    (Normalization.zeroTree_checked q (source_checked q b ha)) hn
    (Normalization.zeroTree_normal q) hr (OmegaQuotient.Support.zero_restricted q b)
  simpa only [hz, Normalization.zeroTree_denote] using he

/-- The genuine actual divided high/residual higher test transports. Every
part caller is constructed by the real decomposition, not supplied. -/
theorem higherParts_transform (q b m : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q b t) :
    FixedPoint.higherCheck (betaCode q b) m
      (Decomposition.highCode m (transform q b t).code)
      (Decomposition.lowCode m (transform q b t).code) =
        FixedPoint.higherCheck q (m + 1)
          (Decomposition.highCode (m + 1) t.code) (Decomposition.lowCode (m + 1) t.code) := by
  have hi := ReturnedIota.original_accepted q t ht hn
  have hp := Decomposition.parts_checked q (m + 1) t.code hi
  have hnp := Decomposition.parts_normal q (m + 1) t.code hi
  have hrp := parts_restricted q b (m + 1) t hr
  have hti := ReturnedIota.original_accepted (betaCode q b) (transform q b t)
    (transform_checked q b ha t ht hr) (transform_normal q b ha t ht hn hr)
  have htp := Decomposition.parts_accepted (betaCode q b) m (transform q b t).code hti
  have hdp := ReturnedIota.original_accepted (betaCode q b)
    (transform q b (Decomposition.highPartTerm (m + 1) t.code))
    (transform_checked q b ha _ hp.1 hrp.1)
    (transform_normal q b ha _ hp.1 hnp.1 hrp.1)
  have hep := ReturnedIota.original_accepted (betaCode q b)
    (transform q b (Decomposition.lowPartTerm (m + 1) t.code))
    (transform_checked q b ha _ hp.2 hrp.2)
    (transform_normal q b ha _ hp.2 hnp.2 hrp.2)
  have hdv : interpretation (betaCode q b) (Decomposition.highCode m (transform q b t).code) =
      interpretation (betaCode q b) (transform q b (Decomposition.highPartTerm (m + 1) t.code)).code := by
    simpa only [Decomposition.highCode, interpretation_code] using
      highPart_transform_value q b m ha t ht hn hr
  have hev : interpretation (betaCode q b) (Decomposition.lowCode m (transform q b t).code) =
      interpretation (betaCode q b) (transform q b (Decomposition.lowPartTerm (m + 1) t.code)).code := by
    simpa only [Decomposition.lowCode, interpretation_code] using
      lowPart_transform_value q b m ha t ht hn hr
  have hlow := Decomposition.lowPart_bound (betaCode q b) m (transform q b t).code hti
  rw [higherCheck_value_invariant (betaCode q b) m _ _ _ _
    htp.1 htp.2 hdp hep hlow (hev ▸ hlow) hdv hev]
  simpa only [Decomposition.highCode, Decomposition.lowCode] using
    higherCheck_transform q b m ha (Decomposition.highPartTerm (m + 1) t.code)
      (Decomposition.lowPartTerm (m + 1) t.code) hp.1 hp.2 hnp.1 hnp.2 hrp.1 hrp.2

/-- The actual source theta caller alone supplies both fixed-test sorts.
The genuine epsilon-source fixed test shifts from m+1 to m under iota. -/
theorem fixedCode_theta_argument_transform (q b m : Nat) (ha : rootCheck q b = true)
    (t : RelativeTerm Nat) (htheta : check q (.theta (m + 1) t) = true)
    (hn : Comparison.Normal q t) (hr : Restricted q b t) :
    FixedPoint.fixedCode (betaCode q b) m (transform q b t).code =
      FixedPoint.fixedCode q (m + 1) t.code := by
  have ht := FixedPoint.checked_theta_argument q (m + 1) t htheta
  have hs : t.outerSort ≤ m + 3 :=
    (denote_lt_iff_outerSort_le q t ht (m + 3) (by omega)).mp
      (by simpa only [Nat.add_assoc] using FixedPoint.checked_theta_sort q (m + 1) t htheta)
  have hi := ReturnedIota.original_accepted q t ht hn
  have hti := ReturnedIota.original_accepted (betaCode q b) (transform q b t)
    (transform_checked q b ha t ht hr) (transform_normal q b ha t ht hn hr)
  have hsource : FixedPoint.inputCheck q (m + 1) t.code = true := by
    simp only [FixedPoint.inputCheck, hi, rawTree_code, Bool.true_and, decide_eq_true_eq]
    omega
  have htarget : FixedPoint.inputCheck (betaCode q b) m (transform q b t).code = true := by
    simp only [FixedPoint.inputCheck, hti, rawTree_code, Bool.true_and, decide_eq_true_eq,
      transform_outerSort_eq q b ha t ht hr]
    omega
  have hp := Decomposition.parts_checked q (m + 1) t.code hi
  have hnp := Decomposition.parts_normal q (m + 1) t.code hi
  have hrp := parts_restricted q b (m + 1) t hr
  have hsourceLow := (Decomposition.parts_accepted q (m + 1) t.code hi).2
  have htargetLow := (Decomposition.parts_accepted (betaCode q b) m (transform q b t).code hti).2
  have hzero : FixedPoint.zeroCheck (Decomposition.lowCode m (transform q b t).code) =
      FixedPoint.zeroCheck (Decomposition.lowCode (m + 1) t.code) := by
    apply Bool.eq_iff_iff.mpr
    rw [FixedPoint.zeroCheck_exact (betaCode q b) _ htargetLow,
      FixedPoint.zeroCheck_exact q _ hsourceLow]
    simpa only [Decomposition.lowCode, interpretation_code,
      lowPart_transform_value q b m ha t ht hn hr] using
      transform_zero_iff q b ha (Decomposition.lowPartTerm (m + 1) t.code) hp.2 hnp.2 hrp.2
  simp only [FixedPoint.fixedCode, hsource, htarget, Bool.true_and, hzero,
    higherParts_transform q b m ha t ht hn hr]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.FixedPointTransport
