import Alexander313.Wilken.SourceOneNativeIotaEnclosureSupport
import Alexander313.Wilken.HereditaryNativeIotaAlphaPlusEquality

/-!
# Genuine original-source-one iota enclosure and lambda endpoint

Simultaneous first-tree size induction uses the ORIGINAL theta atom list and
original exposed comparison to enclose every admitted restricted argument
by the genuine same-index alpha collapse at its ORIGINAL value. The actual
root ANF high part derives every caller. The generic finite/global own-hull
endpoint identity specializes to tau=1, proving the printed original
alpha-plus bound and genuine LOW status of executing source-one lambda.
No Native epsilon source parser at one, enclosure or endpoint oracle.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Enclosure

open OrderSupport
open NativeContext.Iota.OrderInduction (checked_theta_pos_principal checked_theta_lt_iff_exposed)

/-- The first source tree alone controls recursion. The comparison argument
in the second clause may have arbitrary size and hidden native height. -/
private def EnclosureStatement (a fuel : Nat) : Prop :=
  (∀ k (t : RelativeTerm Nat), (.theta k t : RelativeTerm Nat).size ≤ fuel →
    check 0 (.theta k t) = true → Theta.Normal 0 t →
    Restricted a t →
    NativeContext.denote (alphaCode a) (transform a t) <
      NativeContext.denote (alphaCode a) (.theta k (unshifted a t))) ∧
  (∀ k (b : RelativeTerm Nat), (.theta (k + 1) b : RelativeTerm Nat).size ≤ fuel →
    check 0 (.theta (k + 1) b) = true → Theta.Normal 0 b →
    Restricted a (.theta (k + 1) b) → ∀ t : RelativeTerm Nat,
    check 0 (.theta k t) = true → Theta.Normal 0 t →
    Restricted a t →
    denote 0 (.theta (k + 1) b) ≤ denote 0 t →
    NativeContext.denote (alphaCode a) (transform a (.theta (k + 1) b)) <
      NativeContext.denote (alphaCode a) (.theta k (unshifted a t)))

private theorem enclosure_all (a : Nat) (ha : rootCheck a = true) (fuel : Nat) :
    EnclosureStatement a fuel := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    have argument : ∀ k (t : RelativeTerm Nat), (.theta k t : RelativeTerm Nat).size ≤ fuel →
        check 0 (.theta k t) = true → Theta.Normal 0 t →
        Restricted a t →
        NativeContext.denote (alphaCode a) (transform a t) <
          NativeContext.denote (alphaCode a) (.theta k (unshifted a t)) := by
      intro k t hsize ht hn hr
      have hc := argument_checked k t ht
      have htarg := SourceFixedPoint.checked_theta_sort 0 k t ht
      have htarget := unshifted_theta_checked a k ha t ht hr
      have hp := checked_theta_pos_principal _ k (unshifted a t) htarget
      rw [← mapped_atoms_value a ha t hc hn hr]
      apply principalSum_lt hp.1 hp.2
      intro p hpm
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hpm
      have hxc := atoms_checked_normal t x hc hn hx
      have hxr := restricted_atoms a t x hr hx
      have hxv := source_atom_value_le t x hc hn hx
      have hxsort : x.outerSort ≤ k + 2 :=
        (denote_lt_iff_outerSort_le _ x hxc.1 (k + 2) (by omega)).mp (hxv.trans_lt htarg)
      obtain ⟨j, b, rfl⟩ := atoms_shape t x hx
      cases j with
      | zero =>
        exact low_transform_lt_theta a k ha (.theta 0 b) (unshifted a t)
          hxc.1 hxr le_rfl htarget
      | succ j =>
        by_cases hjk : j + 1 ≤ k
        · exact shifted_theta_lt_positive_theta a j k ha b (unshifted a t)
            hxc.1 hxr hjk htarget
        · have hj : j = k := by simp only [outerSort] at hxsort; omega
          subst j
          have hsmall : (.theta (k + 1) b : RelativeTerm Nat).size < fuel :=
            ((thetaAtoms_size_le t _ hx).trans_lt (theta_arg_size_lt k t)).trans_le hsize
          exact (ih _ hsmall).2 k b le_rfl hxc.1 hxc.2 hxr t ht hn hr hxv
    refine ⟨argument, ?_⟩
    intro k b hsize hb hbn hbr t ht htn htr hle
    have hbc := argument_checked (k + 1) b hb
    have hbrr := (restricted_theta_succ a k b).mp hbr
    have hleft := transform_checked a ha (.theta (k + 1) b) hb hbr
    rw [transform_theta_succ a k ha b hb hbr] at hleft ⊢
    have hright := unshifted_theta_checked a k ha t ht htr
    have htc := argument_checked k t ht
    apply (checked_theta_lt_iff_exposed (alphaCode a) k (transform a b) (unshifted a t)
      hleft hright (transform_normal a ha b hbc hbn hbrr)
      (unshifted_normal a ha t htc htn htr)).mpr
    refine Or.inl ⟨?_, ?_⟩
    · have he := argument (k + 1) b hsize hb hbn hbrr
      rw [unshifted_positive_theta_value a (k + 1) ha b hb hbrr (by omega)] at he
      rw [unshifted_value a ha t htc htr]
      exact he.trans_le hle
    · intro x hx
      rw [transform_exposedThetaList a k ha b hbc hbrr] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have hyc := exposed_checked_normal (k + 1) b y hbc hbn hy
      have hyr := restricted_exposed a (k + 1) b y hbrr hy
      have hyv := (source_exposed_lt_root (k + 1) b y hb hbn hy).le.trans hle
      have hsmall : y.size < fuel :=
        ((exposedTheta_size_le (k + 1) b y ((mem_exposedThetaList_iff _ _ _).mp hy)).trans_lt
          (theta_arg_size_lt (k + 1) b)).trans_le hsize
      obtain ⟨c, rfl⟩ := exposed_shape (k + 1) b y hy
      exact (ih _ hsmall).2 k c le_rfl hyc.1 hyc.2 hyr t ht htn htr hyv

/-- Every original normal restricted argument is enclosed by the actual
alpha collapse at the same index and the argument's ORIGINAL value. -/
theorem transform_argument_lt_theta (a k : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : check 0 (.theta k t) = true)
    (hn : Theta.Normal 0 t) (hr : Restricted a t) :
    NativeContext.denote (alphaCode a) (transform a t) <
      NativeContext.denote (alphaCode a) (.theta k (unshifted a t)) :=
  (enclosure_all a ha (.theta k t : RelativeTerm Nat).size).1 k t le_rfl ht hn hr

/-- The comparison argument retains only its original restriction; it is
not required to be a precomputed image or to have bounded hidden height. -/
theorem transform_theta_lt_enclosing_theta (a k : Nat) (ha : rootCheck a = true)
    (b t : RelativeTerm Nat) (hb : check 0 (.theta (k + 1) b) = true)
    (hbn : Theta.Normal 0 b) (hbr : Restricted a (.theta (k + 1) b))
    (ht : check 0 (.theta k t) = true)
    (htn : Theta.Normal 0 t) (htr : Restricted a t)
    (hle : denote 0 (.theta (k + 1) b) ≤ denote 0 t) :
    NativeContext.denote (alphaCode a) (transform a (.theta (k + 1) b)) <
      NativeContext.denote (alphaCode a) (.theta k (unshifted a t)) :=
  (enclosure_all a ha (.theta (k + 1) b : RelativeTerm Nat).size).2
    k b le_rfl hb hbn hbr t ht htn htr hle

theorem transform_argument_lt_source_positive_theta (a k : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : check 0 (.theta k t) = true)
    (hn : Theta.Normal 0 t) (hr : Restricted a t) (hk : 0 < k) :
    NativeContext.denote (alphaCode a) (transform a t) < denote 0 (.theta k t) := by
  rw [← unshifted_positive_theta_value a k ha t ht hr hk]
  exact transform_argument_lt_theta a k ha t ht hn hr

def deltaTerm (a : Nat) : RelativeTerm Nat :=
  SourceDecomposition.highPartTerm 0 0 (Lambda.argumentCode a)

def deltaEnclosureTerm (a : Nat) : RelativeTerm Nat := .theta 0 (unshifted a (deltaTerm a))

theorem delta_theta_checked (a : Nat) (ha : rootCheck a = true) : check 0 (.theta 0 (deltaTerm a)) = true := by
  have hc := Lambda.argument_accepted a ha
  have hp := (SourceDecomposition.parts_checked 0 0 (Lambda.argumentCode a) hc).1
  have hs : interpretation 0 (Lambda.argumentCode a) < omegaSequence (finiteBase 0) 2 := by
    obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact a).mp ha
    simpa only [OmegaQuotient.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      SourceFixedPoint.checked_theta_sort 0 0 t ht
  have hd := (SourceDecomposition.parts_sort 0 0 (Lambda.argumentCode a) hc hs).1
  apply Inverse.checked_theta 0 (deltaTerm a) hp
  exact (denote_lt_iff_outerSort_le 0 _ hp 2 (by omega)).mp hd

theorem delta_enclosure_spec (a : Nat) (ha : rootCheck a = true) :
    NativeContext.check (alphaCode a) (deltaEnclosureTerm a) = true ∧
      NativeContext.Comparison.Normal (alphaCode a) (deltaEnclosureTerm a) ∧
      NativeContext.denote (alphaCode a) (deltaEnclosureTerm a) =
        globalCollapse (NativeContext.base (alphaCode a)) 0 (interpretation 0 (Lambda.deltaCode a)) ∧
      interpretation 0 a < NativeContext.denote (alphaCode a) (deltaEnclosureTerm a) := by
  have hc := Lambda.argument_accepted a ha
  have hp := (SourceDecomposition.parts_checked 0 0 (Lambda.argumentCode a) hc).1
  have hn := (SourceDecomposition.parts_normal 0 0 (Lambda.argumentCode a) hc).1
  have hr := Lambda.delta_restricted a ha
  have ht := unshifted_theta_checked a 0 ha (deltaTerm a) (delta_theta_checked a ha) hr
  have hnt := unshifted_normal a ha (deltaTerm a) hp hn hr
  have hv : NativeContext.denote (alphaCode a) (unshifted a (deltaTerm a)) =
      interpretation 0 (Lambda.deltaCode a) := by
    simpa only [OmegaQuotient.deltaCode, SourceDecomposition.highCode, interpretation_code, deltaTerm] using
      unshifted_value a ha (deltaTerm a) hp hr
  refine ⟨ht, hnt, ?_, ?_⟩
  · change globalCollapse (NativeContext.base (alphaCode a)) 0
      (NativeContext.denote (alphaCode a) (unshifted a (deltaTerm a))) = _
    rw [hv]
  · rw [← alpha_base a ha]
    exact (NativeContext.SourceChi.Arithmetic.proper_theta_zero_iff _ _ ht hnt).mpr
      (by rw [hv]; exact Lambda.delta_nonzero a ha)

theorem literalDelta_lt_enclosure (a : Nat) (ha : rootCheck a = true) :
    NativeContext.interpretation (alphaCode a) (literalCode a (Lambda.deltaCode a)) <
      NativeContext.denote (alphaCode a) (deltaEnclosureTerm a) := by
  have hc := Lambda.argument_accepted a ha
  have hn := (SourceDecomposition.parts_normal 0 0 (Lambda.argumentCode a) hc).1
  have hp := (SourceDecomposition.parts_checked 0 0 (Lambda.argumentCode a) hc).1
  have hr := Lambda.delta_restricted a ha
  have hh := transform_argument_lt_theta a 0 ha (deltaTerm a) (delta_theta_checked a ha) hn hr
  have he : literalCode a (Lambda.deltaCode a) = (transform a (deltaTerm a)).code :=
    literalCode_code a ha (deltaTerm a) hp hn hr
  simpa only [he, NativeContext.interpretation_code, deltaEnclosureTerm] using hh

theorem lambda_lt_enclosure (a out : Nat) (ho : out ∈ Lambda.execute a) :
    NativeContext.interpretation (alphaCode a) out < NativeContext.denote (alphaCode a) (deltaEnclosureTerm a) := by
  have hs := Lambda.execute_spec a out ho
  have ha : rootCheck a = true := hs.1
  obtain ⟨d, hd, hdc, hdv⟩ := SourceZeta.zeta_returns 0 a (Bool.and_eq_true.mp ha).1
  have hz := SourceZeta.zeta_bound 0 a d hd
  have hp := checked_theta_pos_principal (alphaCode a) 0 (unshifted a (deltaTerm a))
    (delta_enclosure_spec a ha).1
  rw [hs.2.2]
  exact hp.2 (literalDelta_lt_enclosure a ha)
    (hdv.symm.trans_lt (hz.trans (delta_enclosure_spec a ha).2.2.2))

noncomputable def sourceAlphaPlus (a : Nat) : Ordinal.{0} :=
  globalCollapse (finiteBase 0) 0 (interpretation 0 (Lambda.argumentCode a) + 1)

theorem delta_enclosure_eq_sourceAlphaPlus (a : Nat) (ha : rootCheck a = true) :
    NativeContext.denote (alphaCode a) (deltaEnclosureTerm a) = sourceAlphaPlus a := by
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact a).mp ha
  have hc := Lambda.argument_accepted a ha
  have htarg := argument_checked 0 t ht
  have hA : GlobalNotation (finiteBase 0) 1 (interpretation 0 (Lambda.argumentCode a)) := by
    simpa only [OmegaQuotient.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      SourceDecomposition.checked_all_levels 0 1 t htarg
  have hAs : interpretation 0 (Lambda.argumentCode a) < omegaSequence (finiteBase 0) 2 := by
    simpa only [OmegaQuotient.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      SourceFixedPoint.checked_theta_sort 0 0 t ht
  have hroot : interpretation 0 a = globalCollapse (finiteBase 0) 0
      (interpretation 0 (Lambda.argumentCode a)) := by
    simp only [he, OmegaQuotient.argumentCode, Localization.argumentCode_theta, interpretation_code]
    rfl
  have hΔ0 : 0 < interpretation 0 (Lambda.deltaCode a) :=
    lt_of_le_of_ne (zero_le _) (Lambda.delta_nonzero a ha).symm
  have hb := NativeContext.Iota.AlphaPlus.global_relative_highPart_eq_source_successor
    (finiteBase 0) (finiteBase_pos 0) (interpretation 0 (Lambda.argumentCode a))
    (interpretation 0 (Lambda.deltaCode a))
    (interpretation 0 (SourceDecomposition.lowCode 0 0 (Lambda.argumentCode a))) hA hAs
    (SourceDecomposition.highPart_dvd 0 0 (Lambda.argumentCode a) hc) hΔ0
    (SourceDecomposition.lowPart_bound 0 0 (Lambda.argumentCode a) hc)
    (SourceDecomposition.parts_reconstruct 0 0 (Lambda.argumentCode a) hc).symm
  rw [(delta_enclosure_spec a ha).2.2.1, alpha_base a ha, hroot]
  exact hb

theorem source_lemma_2_46_a (a : Nat) (ha : rootCheck a = true) :
    NativeContext.interpretation (alphaCode a) (literalCode a (Lambda.deltaCode a)) < sourceAlphaPlus a := by
  rw [← delta_enclosure_eq_sourceAlphaPlus a ha]
  exact literalDelta_lt_enclosure a ha

theorem source_lemma_2_48_b (a out : Nat) (ho : out ∈ Lambda.execute a) :
    NativeContext.interpretation (alphaCode a) out < sourceAlphaPlus a := by
  rw [← delta_enclosure_eq_sourceAlphaPlus a (Lambda.execute_spec a out ho).1]
  exact lambda_lt_enclosure a out ho

theorem lambda_low (a out : Nat) (ho : out ∈ Lambda.execute a) :
    NativeContext.lowCheckCode (alphaCode a) out = true := by
  have hs := Lambda.execute_spec a out ho
  apply NativeContext.OmegaPowers.low_of_bound _ out
    ((NativeContext.Comparison.acceptedCode_exact _ _).mp hs.2.1).1
  exact (lambda_lt_enclosure a out ho).trans
    (NativeContext.FixedPoint.checked_theta_range (alphaCode a) 0
      (unshifted a (deltaTerm a)) (delta_enclosure_spec a hs.1).1).2

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Enclosure
