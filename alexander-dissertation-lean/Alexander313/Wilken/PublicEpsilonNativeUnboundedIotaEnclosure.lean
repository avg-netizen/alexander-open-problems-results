import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaEnclosureSupport
import Alexander313.Wilken.PublicEpsilonNativeRootEndpointCollapse

/-!
# Actual same-index collapse enclosure on the full original iota domain

Simultaneous syntax-size induction derives all exposed comparison bounds.
The actual mapped Delta is strictly below beta's zero-family collapse of
Delta's ORIGINAL value. A genuine original-head scalar call identifies
that endpoint with the original source argument successor; no endpoint,
support, translated presentation or enclosure premise is supplied.
Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Enclosure

open ThetaCourse
open OrderSupport
open Iota.OrderInduction

/-- The first source tree alone controls recursion. The comparison argument
in the second clause may have arbitrary size and hidden native height. -/
private def EnclosureStatement (q root fuel : Nat) : Prop :=
  (∀ k (t : RelativeTerm Nat), (.theta k t : RelativeTerm Nat).size ≤ fuel →
    check (q) (.theta k t) = true → Comparison.Normal (q) t →
    Restricted q root t →
    denote (betaCode q root) (transform q root t) <
      denote (betaCode q root) (.theta k (unshifted q root t))) ∧
  (∀ k (b : RelativeTerm Nat), (.theta (k + 1) b : RelativeTerm Nat).size ≤ fuel →
    check (q) (.theta (k + 1) b) = true → Comparison.Normal (q) b →
    Restricted q root (.theta (k + 1) b) → ∀ t : RelativeTerm Nat,
    check (q) (.theta k t) = true → Comparison.Normal (q) t →
    Restricted q root t →
    denote (q) (.theta (k + 1) b) ≤ denote (q) t →
    denote (betaCode q root) (transform q root (.theta (k + 1) b)) <
      denote (betaCode q root) (.theta k (unshifted q root t)))

private theorem enclosure_all (q root : Nat) (ha : rootCheck q root = true) (fuel : Nat) :
    EnclosureStatement q root fuel := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    have argument : ∀ k (t : RelativeTerm Nat), (.theta k t : RelativeTerm Nat).size ≤ fuel →
        check (q) (.theta k t) = true → Comparison.Normal (q) t →
        Restricted q root t →
        denote (betaCode q root) (transform q root t) <
          denote (betaCode q root) (.theta k (unshifted q root t)) := by
      intro k t hsize ht hn hr
      have hc := BaseTransformation.theta_argument_check _ k t ht
      have htarg := FixedPoint.checked_theta_sort _ k t ht
      have htarget := unshifted_theta_checked q root k ha t ht hr
      have hp := checked_theta_pos_principal _ k (unshifted q root t) htarget
      rw [← mapped_atoms_value q root ha t hc hn hr]
      apply principalSum_lt hp.1 hp.2
      intro p hpm
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hpm
      have hxc := atoms_checked_normal _ t x hc hn hx
      have hxr := restricted_atoms q root t x hr hx
      have hxv := Iota.Enclosure.source_atom_value_le _ t x hc hn hx
      have hxsort : x.outerSort ≤ k + 2 :=
        (denote_lt_iff_outerSort_le _ x hxc.1 (k + 2) (by omega)).mp (hxv.trans_lt htarg)
      rcases Iota.Addition.atoms_shape t x hx with ⟨p, rfl⟩ | ⟨j, b, rfl⟩
      · exact low_transform_lt_theta q root k ha (.parameter p) (unshifted q root t)
          hxc.1 hxr (Nat.zero_le _) htarget
      · cases j with
        | zero =>
          exact low_transform_lt_theta q root k ha (.theta 0 b) (unshifted q root t)
            hxc.1 hxr le_rfl htarget
        | succ j =>
          by_cases hjk : j + 1 ≤ k
          · exact shifted_theta_lt_positive_theta q root j k ha b (unshifted q root t)
              hxc.1 hxr hjk htarget
          · have hj : j = k := by simp only [outerSort] at hxsort; omega
            subst j
            have hsmall : (.theta (k + 1) b : RelativeTerm Nat).size < fuel :=
              ((Comparison.atoms_size_le t _ hx).trans_lt (theta_arg_size_lt k t)).trans_le hsize
            exact (ih _ hsmall).2 k b le_rfl hxc.1 hxc.2 hxr t ht hn hr hxv
    refine ⟨argument, ?_⟩
    intro k b hsize hb hbn hbr t ht htn htr hle
    have hbc := BaseTransformation.theta_argument_check _ (k + 1) b hb
    have hbrr := (restricted_theta_succ q root k b).mp hbr
    have hleft := transform_checked q root ha (.theta (k + 1) b) hb hbr
    rw [transform_theta_succ q root k ha b hb hbr] at hleft ⊢
    have hright := unshifted_theta_checked q root k ha t ht htr
    have htc := BaseTransformation.theta_argument_check _ k t ht
    apply (checked_theta_lt_iff_exposed (betaCode q root) k (transform q root b) (unshifted q root t)
      hleft hright (transform_normal q root ha b hbc hbn hbrr)
      (unshifted_normal q root ha t htc htn htr)).mpr
    refine Or.inl ⟨?_, ?_⟩
    · have he := argument (k + 1) b hsize hb hbn hbrr
      rw [unshifted_positive_theta_value q root (k + 1) ha b hb hbrr (by omega)] at he
      rw [unshifted_value q root ha t htc htr]
      exact he.trans_le hle
    · intro x hx
      rw [transform_exposedThetaList q root k ha b hbc hbrr] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have hyc := exposed_checked_normal _ (k + 1) b y hbc hbn hy
      have hyr := restricted_exposed q root (k + 1) b y hbrr hy
      have hyv := (Iota.Enclosure.source_exposed_lt_root _ (k + 1) b y hb hbn hy).le.trans hle
      have hsmall : y.size < fuel :=
        ((exposedTheta_size_le (k + 1) b y ((mem_exposedThetaList_iff _ _ _).mp hy)).trans_lt
          (theta_arg_size_lt (k + 1) b)).trans_le hsize
      obtain ⟨c, rfl⟩ := Iota.Enclosure.exposed_shape (k + 1) b y hy
      exact (ih _ hsmall).2 k c le_rfl hyc.1 hyc.2 hyr t ht htn htr hyv

/-- Every original normal restricted argument is enclosed by the actual
alpha collapse at the same index and the argument's ORIGINAL value. -/
theorem transform_argument_lt_theta (q root k : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) (.theta k t) = true)
    (hn : Comparison.Normal (q) t) (hr : Restricted q root t) :
    denote (betaCode q root) (transform q root t) <
      denote (betaCode q root) (.theta k (unshifted q root t)) :=
  (enclosure_all q root ha (.theta k t : RelativeTerm Nat).size).1 k t le_rfl ht hn hr

/-- The comparison argument retains only its original restriction; it is
not required to be a precomputed image or to have bounded hidden height. -/
theorem transform_theta_lt_enclosing_theta (q root k : Nat) (ha : rootCheck q root = true)
    (b t : RelativeTerm Nat) (hb : check (q) (.theta (k + 1) b) = true)
    (hbn : Comparison.Normal (q) b) (hbr : Restricted q root (.theta (k + 1) b))
    (ht : check (q) (.theta k t) = true)
    (htn : Comparison.Normal (q) t) (htr : Restricted q root t)
    (hle : denote (q) (.theta (k + 1) b) ≤ denote (q) t) :
    denote (betaCode q root) (transform q root (.theta (k + 1) b)) <
      denote (betaCode q root) (.theta k (unshifted q root t)) :=
  (enclosure_all q root ha (.theta (k + 1) b : RelativeTerm Nat).size).2
    k b le_rfl hb hbn hbr t ht htn htr hle

theorem transform_argument_lt_source_positive_theta (q root k : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check (q) (.theta k t) = true)
    (hn : Comparison.Normal (q) t) (hr : Restricted q root t) (hk : 0 < k) :
    denote (betaCode q root) (transform q root t) < denote (q) (.theta k t) := by
  rw [← unshifted_positive_theta_value q root k ha t ht hr hk]
  exact transform_argument_lt_theta q root k ha t ht hn hr

def deltaTerm (root : Nat) : RelativeTerm Nat := rawTree (OmegaQuotient.deltaCode root)

theorem delta_original (q root : Nat) (ha : rootCheck q root = true) :
    check q (deltaTerm root) = true ∧ Comparison.Normal q (deltaTerm root) ∧
      Restricted q root (deltaTerm root) := by
  obtain ⟨_, t, he, ht, hn, hs⟩ := (inputCheck_exact q root _).mp (Lambda.delta_input q root ha)
  have hr := (restricted_iff_sourceStar q root ha t ht hn).mpr hs
  simpa only [deltaTerm, he, rawTree_code] using And.intro ht (And.intro hn hr)

theorem delta_theta_checked (q root : Nat) (ha : rootCheck q root = true) :
    check q (.theta 0 (deltaTerm root)) = true := by
  have hd := delta_original q root ha
  have hc := ((Comparison.acceptedCode_exact q _).mp (LambdaSource.delta_accepted q root ha)).1
  have hs : (deltaTerm root).outerSort ≤ 2 :=
    (denote_lt_iff_outerSort_le q _ hd.1 2 (by omega)).mp
      (by rw [show denote q (deltaTerm root) = interpretation q (OmegaQuotient.deltaCode root)
        from Arithmetic.raw_value q _ hc]; exact LambdaSource.delta_below_second q root ha)
  exact RootPositiveCollapse.theta_checked q 0 _ hd.1 hs

def deltaEnclosureTerm (q root : Nat) : RelativeTerm Nat :=
  .theta 0 (unshifted q root (deltaTerm root))

/-- The endpoint uses the ORIGINAL q-context argument successor from
Convention2.28. It is not an invented successor on beta parameters. -/
noncomputable def sourceAlphaPlus (q root : Nat) : Ordinal.{0} :=
  globalCollapse (base q) 0 (interpretation q (Localization.argumentCode root) + 1)

theorem delta_enclosure_spec (q root : Nat) (ha : rootCheck q root = true) :
    check (betaCode q root) (deltaEnclosureTerm q root) = true ∧
      Comparison.Normal (betaCode q root) (deltaEnclosureTerm q root) ∧
      denote (betaCode q root) (deltaEnclosureTerm q root) =
        globalCollapse (base (betaCode q root)) 0
          (interpretation q (OmegaQuotient.deltaCode root)) := by
  have hd := delta_original q root ha
  have hc := ((Comparison.acceptedCode_exact q _).mp (LambdaSource.delta_accepted q root ha)).1
  refine ⟨unshifted_theta_checked q root 0 ha _ (delta_theta_checked q root ha) hd.2.2,
    unshifted_normal q root ha _ hd.1 hd.2.1 hd.2.2, ?_⟩
  change globalCollapse (base (betaCode q root)) 0
    (denote (betaCode q root) (unshifted q root (deltaTerm root))) = _
  rw [unshifted_value q root ha _ hd.1 hd.2.2]
  exact congrArg (globalCollapse (base (betaCode q root)) 0) (Arithmetic.raw_value q _ hc)

/-- A genuine scalar call at the admitted zero tail identifies the actual
beta enclosure with the ORIGINAL source successor, without a ceiling oracle. -/
theorem delta_enclosure_value (q root : Nat) (ha : rootCheck q root = true) :
    denote (betaCode q root) (deltaEnclosureTerm q root) = sourceAlphaPlus q root := by
  have hz := OmegaPowerHeight.numeralCode_spec q 0 (source_checked q root ha)
  have hi : RootEndpointCollapse.inputCheck q root (OmegaPowerHeight.numeralCode 0) = true :=
    (RootLowCollapse.inputCheck_exact q root _).mpr ⟨ha, hz.1⟩
  have hc := RootEndpointCollapse.collapseCode_spec q root _ hi
  have hs := RootEndpointCollapse.successorArgumentCode_spec q root _ hi
  have ht := RootEndpointCollapse.thetaCode_sorted_spec q _ hs.1 hs.2.2
  have hv : interpretation q (RootEndpointCollapse.collapseCode q root
      (OmegaPowerHeight.numeralCode 0)) = sourceAlphaPlus q root := by
    simpa only [RootEndpointCollapse.collapseCode, hi, Bool.cond_true,
      hs.2.1, hz.2.2.1, Nat.cast_zero, add_zero, sourceAlphaPlus,
      RootEndpointCollapse.argumentCode] using ht.2.2
  rw [(delta_enclosure_spec q root ha).2.2, beta_base q root ha]
  have he := hc.2.2
  rw [hz.2.2.1, Nat.cast_zero, add_zero] at he
  exact he.symm.trans hv

/-- The original alpha-plus has a concrete checked Normal LOW beta-context
code. This is an actual source-to-beta boundary witness, not a supplied
representation or interval ceiling. -/
theorem delta_enclosure_code_spec (q root : Nat) (ha : rootCheck q root = true) :
    lowCheckCode (betaCode q root) (deltaEnclosureTerm q root).code = true ∧
      Comparison.acceptedCode (betaCode q root) (deltaEnclosureTerm q root).code = true ∧
      interpretation (betaCode q root) (deltaEnclosureTerm q root).code = sourceAlphaPlus q root := by
  have hs := delta_enclosure_spec q root ha
  refine ⟨?_, (Comparison.acceptedCode_exact _ _).mpr ?_, ?_⟩
  · simp only [lowCheckCode_code, lowCheck, hs.1, deltaEnclosureTerm,
      RelativeTerm.outerSort, Nat.zero_add, le_refl, decide_true, Bool.true_and]
  · simpa only [checkCode_code, rawTree_code] using And.intro hs.1 hs.2.1
  · simpa only [interpretation_code] using delta_enclosure_value q root ha

theorem root_lt_enclosure (q root : Nat) (ha : rootCheck q root = true) :
    interpretation q root < denote (betaCode q root) (deltaEnclosureTerm q root) := by
  have hd := delta_original q root ha
  have hs := delta_enclosure_spec q root ha
  rw [← beta_base q root ha]
  apply (SourceChi.Arithmetic.proper_theta_zero_iff _ _ hs.1 hs.2.1).mpr
  rw [unshifted_value q root ha _ hd.1 hd.2.2]
  have hc := ((Comparison.acceptedCode_exact q _).mp (LambdaSource.delta_accepted q root ha)).1
  rw [Arithmetic.raw_value q _ hc]
  exact ne_of_gt (RootEndpointCollapse.delta_positive q root ha)

theorem sourceAlphaPlus_epsilon (q root : Nat) (ha : rootCheck q root = true) :
    Ordinal.omega0 ^ sourceAlphaPlus q root = sourceAlphaPlus q root := by
  have hf := RootEndpointCollapse.firstCode_spec q root ha
  have hhs : interpretation q (RootEndpointCollapse.firstCode q root) < omegaSequence (base q) 2 := by
    rw [hf.2]
    exact (omegaSequence_isSuccLimit (base q) 1).add_one_lt
      (RootEndpointCollapse.argument_sorted q root ha)
  have hc := Arithmetic.raw_checked q _ ((Comparison.acceptedCode_exact q _).mp hf.1).1
  have hn := RootPositiveCollapse.theta_checked q 0 _ hc
    ((denote_lt_iff_outerSort_le q _ hc 2 (by omega)).mp
      (by rw [Arithmetic.raw_value q _ ((Comparison.acceptedCode_exact q _).mp hf.1).1]; exact hhs))
  have he := (OmegaPowers.theta_epsilon_iff q _ hn).mpr (Or.inr (by
    rw [Arithmetic.raw_value q _ ((Comparison.acceptedCode_exact q _).mp hf.1).1, hf.2]
    exact (RootEndpointCollapse.argument_not_low q root ha).trans le_self_add))
  change Ordinal.omega0 ^ globalCollapse (base q) 0
    (denote q (rawTree (RootEndpointCollapse.firstCode q root))) =
      globalCollapse (base q) 0 (denote q (rawTree (RootEndpointCollapse.firstCode q root))) at he
  rw [Arithmetic.raw_value q _ ((Comparison.acceptedCode_exact q _).mp hf.1).1, hf.2] at he
  exact he

theorem literalDelta_lt_enclosure (q root : Nat) (ha : rootCheck q root = true) :
    interpretation (betaCode q root) (literalCode q root (OmegaQuotient.deltaCode root)) <
      denote (betaCode q root) (deltaEnclosureTerm q root) := by
  have hd := delta_original q root ha
  have hh := transform_argument_lt_theta q root 0 ha _ (delta_theta_checked q root ha) hd.2.1 hd.2.2
  have hc := ((Comparison.acceptedCode_exact q _).mp (LambdaSource.delta_accepted q root ha)).1
  obtain ⟨t, he, ht⟩ := (checkCode_exact q _).mp hc
  have hn : Comparison.Normal q t := by
    simpa only [← he, rawTree_code] using
      ((Comparison.acceptedCode_exact q _).mp (LambdaSource.delta_accepted q root ha)).2
  have hr : Restricted q root t := by simpa only [deltaTerm, ← he, rawTree_code] using hd.2.2
  simpa only [deltaTerm, ← he, rawTree_code, literalCode_code q root ha t ht hn hr,
    interpretation_code, deltaEnclosureTerm] using hh

/-- The actual executing HIGH lambda has the same genuine strict enclosure. -/
theorem lambda_lt_enclosure (q root out : Nat) (ho : out ∈ Lambda.execute q root) :
    interpretation (betaCode q root) out < denote (betaCode q root) (deltaEnclosureTerm q root) := by
  have hs := Lambda.execute_spec q root out ho
  have hp := checked_theta_pos_principal _ 0 (unshifted q root (deltaTerm root))
    (delta_enclosure_spec q root hs.1).1
  rw [hs.2.2.2, Lambda.sourceValue]
  exact hp.2 (literalDelta_lt_enclosure q root hs.1)
    ((Lambda.zeta_value_lt_root q root hs.1).trans (root_lt_enclosure q root hs.1))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Enclosure
