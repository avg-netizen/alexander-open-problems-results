import Alexander313.Wilken.HereditaryNativeIotaEnclosureSupport

/-!
# Genuine collapse enclosure for the actual iota shift

A simultaneous first-tree size induction derives two actual bounds. The
transformed argument of ANY original admitted theta node is below the real
same-index alpha collapse of the argument's ORIGINAL value. A source node
at index k+1 below another original argument is transformed strictly below
that argument's actual alpha theta-k collapse. The same-level comparison
queries descend through the real exposed list; all support bounds are
derived from original admission and Normality.

Applied to the root's actual ANF high part, this proves iota(Delta) below
the actual alpha theta-zero collapse of ORIGINAL Delta. Identification of
that concrete collapse with the printed alpha-plus is separate. No such
identification or enclosure oracle is assumed. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.Enclosure

open NativePublicBridge (contextCode contextCode_checked)
open OrderInduction

/-- The first source tree alone controls recursion. The comparison argument
in the second clause may have arbitrary size and hidden native height. -/
private def EnclosureStatement (s a fuel : Nat) : Prop :=
  (∀ k (t : RelativeTerm Nat), (.theta k t : RelativeTerm Nat).size ≤ fuel →
    check (contextCode s) (.theta k t) = true → Comparison.Normal (contextCode s) t →
    Restricted s a t →
    denote (alphaCode s a) (transform s a t) <
      denote (alphaCode s a) (.theta k (unshifted s a t))) ∧
  (∀ k (b : RelativeTerm Nat), (.theta (k + 1) b : RelativeTerm Nat).size ≤ fuel →
    check (contextCode s) (.theta (k + 1) b) = true → Comparison.Normal (contextCode s) b →
    Restricted s a (.theta (k + 1) b) → ∀ t : RelativeTerm Nat,
    check (contextCode s) (.theta k t) = true → Comparison.Normal (contextCode s) t →
    Restricted s a t →
    denote (contextCode s) (.theta (k + 1) b) ≤ denote (contextCode s) t →
    denote (alphaCode s a) (transform s a (.theta (k + 1) b)) <
      denote (alphaCode s a) (.theta k (unshifted s a t)))

private theorem enclosure_all (s a : Nat) (ha : rootCheck s a = true) (fuel : Nat) :
    EnclosureStatement s a fuel := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    have argument : ∀ k (t : RelativeTerm Nat), (.theta k t : RelativeTerm Nat).size ≤ fuel →
        check (contextCode s) (.theta k t) = true → Comparison.Normal (contextCode s) t →
        Restricted s a t →
        denote (alphaCode s a) (transform s a t) <
          denote (alphaCode s a) (.theta k (unshifted s a t)) := by
      intro k t hsize ht hn hr
      have hc := BaseTransformation.theta_argument_check _ k t ht
      have htarg := FixedPoint.checked_theta_sort _ k t ht
      have htarget := unshifted_theta_checked s a k ha t ht hr
      have hp := checked_theta_pos_principal _ k (unshifted s a t) htarget
      rw [← mapped_atoms_value s a ha t hc hn hr]
      apply principalSum_lt hp.1 hp.2
      intro p hpm
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hpm
      have hxc := atoms_checked_normal _ t x hc hn hx
      have hxr := restricted_atoms s a t x hr hx
      have hxv := source_atom_value_le _ t x hc hn hx
      have hxsort : x.outerSort ≤ k + 2 :=
        (denote_lt_iff_outerSort_le _ x hxc.1 (k + 2) (by omega)).mp (hxv.trans_lt htarg)
      rcases Addition.atoms_shape t x hx with ⟨p, rfl⟩ | ⟨j, b, rfl⟩
      · exact low_transform_lt_theta s a k ha (.parameter p) (unshifted s a t)
          hxc.1 hxr (Nat.zero_le _) htarget
      · cases j with
        | zero =>
          exact low_transform_lt_theta s a k ha (.theta 0 b) (unshifted s a t)
            hxc.1 hxr le_rfl htarget
        | succ j =>
          by_cases hjk : j + 1 ≤ k
          · exact shifted_theta_lt_positive_theta s a j k ha b (unshifted s a t)
              hxc.1 hxr hjk htarget
          · have hj : j = k := by simp only [outerSort] at hxsort; omega
            subst j
            have hsmall : (.theta (k + 1) b : RelativeTerm Nat).size < fuel :=
              ((Comparison.atoms_size_le t _ hx).trans_lt (theta_arg_size_lt k t)).trans_le hsize
            exact (ih _ hsmall).2 k b le_rfl hxc.1 hxc.2 hxr t ht hn hr hxv
    refine ⟨argument, ?_⟩
    intro k b hsize hb hbn hbr t ht htn htr hle
    have hbc := BaseTransformation.theta_argument_check _ (k + 1) b hb
    have hbrr := (restricted_theta_succ s a k b).mp hbr
    have hleft := transform_checked s a ha (.theta (k + 1) b) hb hbr
    rw [transform_theta_succ s a k ha b hb hbr] at hleft ⊢
    have hright := unshifted_theta_checked s a k ha t ht htr
    have htc := BaseTransformation.theta_argument_check _ k t ht
    apply (checked_theta_lt_iff_exposed (alphaCode s a) k (transform s a b) (unshifted s a t)
      hleft hright (transform_normal s a ha b hbc hbn hbrr)
      (unshifted_normal s a ha t htc htn htr)).mpr
    refine Or.inl ⟨?_, ?_⟩
    · have he := argument (k + 1) b hsize hb hbn hbrr
      rw [unshifted_positive_theta_value s a (k + 1) ha b hb hbrr (by omega)] at he
      rw [unshifted_value s a ha t htc htr]
      exact he.trans_le hle
    · intro x hx
      rw [transform_exposedThetaList s a k ha b hbc hbrr] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have hyc := exposed_checked_normal _ (k + 1) b y hbc hbn hy
      have hyr := restricted_exposed s a (k + 1) b y hbrr hy
      have hyv := (source_exposed_lt_root _ (k + 1) b y hb hbn hy).le.trans hle
      have hsmall : y.size < fuel :=
        ((exposedTheta_size_le (k + 1) b y ((mem_exposedThetaList_iff _ _ _).mp hy)).trans_lt
          (theta_arg_size_lt (k + 1) b)).trans_le hsize
      obtain ⟨c, rfl⟩ := exposed_shape (k + 1) b y hy
      exact (ih _ hsmall).2 k c le_rfl hyc.1 hyc.2 hyr t ht htn htr hyv

/-- Every original normal restricted argument is enclosed by the actual
alpha collapse at the same index and the argument's ORIGINAL value. -/
theorem transform_argument_lt_theta (s a k : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) (.theta k t) = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Restricted s a t) :
    denote (alphaCode s a) (transform s a t) <
      denote (alphaCode s a) (.theta k (unshifted s a t)) :=
  (enclosure_all s a ha (.theta k t : RelativeTerm Nat).size).1 k t le_rfl ht hn hr

/-- The comparison argument retains only its original restriction; it is
not required to be a precomputed image or to have bounded hidden height. -/
theorem transform_theta_lt_enclosing_theta (s a k : Nat) (ha : rootCheck s a = true)
    (b t : RelativeTerm Nat) (hb : check (contextCode s) (.theta (k + 1) b) = true)
    (hbn : Comparison.Normal (contextCode s) b) (hbr : Restricted s a (.theta (k + 1) b))
    (ht : check (contextCode s) (.theta k t) = true)
    (htn : Comparison.Normal (contextCode s) t) (htr : Restricted s a t)
    (hle : denote (contextCode s) (.theta (k + 1) b) ≤ denote (contextCode s) t) :
    denote (alphaCode s a) (transform s a (.theta (k + 1) b)) <
      denote (alphaCode s a) (.theta k (unshifted s a t)) :=
  (enclosure_all s a ha (.theta (k + 1) b : RelativeTerm Nat).size).2
    k b le_rfl hb hbn hbr t ht htn htr hle

theorem transform_argument_lt_source_positive_theta (s a k : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) (.theta k t) = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Restricted s a t) (hk : 0 < k) :
    denote (alphaCode s a) (transform s a t) < denote (contextCode s) (.theta k t) := by
  rw [← unshifted_positive_theta_value s a k ha t ht hr hk]
  exact transform_argument_lt_theta s a k ha t ht hn hr

def deltaTerm (a : Nat) : RelativeTerm Nat :=
  Decomposition.highPartTerm 0 (Lambda.argumentCode a)

/-- The concrete actual target collapse at the ORIGINAL high-part value.
This is not defined to be an arbitrary epsilon successor predicate. -/
def deltaEnclosureTerm (s a : Nat) : RelativeTerm Nat :=
  .theta 0 (unshifted s a (deltaTerm a))

theorem delta_theta_checked (s a : Nat) (ha : rootCheck s a = true) :
    check (contextCode s) (.theta 0 (deltaTerm a)) = true := by
  have hc := Lambda.argument_accepted s a ha
  have hp := (Decomposition.parts_checked (contextCode s) 0 (Lambda.argumentCode a) hc).1
  have hs : interpretation (contextCode s) (Lambda.argumentCode a) <
      omegaSequence (base (contextCode s)) 2 := by
    obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact s a).mp ha
    simpa only [Lambda.argumentCode, he, Localization.argumentCode_theta, interpretation_code] using
      FixedPoint.checked_theta_sort (contextCode s) 0 t ht
  have hd := (Decomposition.parts_sort (contextCode s) 0 (Lambda.argumentCode a) hc hs).1
  apply Inverse.checked_theta (contextCode s) 0 (deltaTerm a) hp
  exact (denote_lt_iff_outerSort_le _ _ hp 2 (by omega)).mp hd

theorem delta_enclosure_spec (s a : Nat) (ha : rootCheck s a = true) :
    check (alphaCode s a) (deltaEnclosureTerm s a) = true ∧
      Comparison.Normal (alphaCode s a) (deltaEnclosureTerm s a) ∧
      denote (alphaCode s a) (deltaEnclosureTerm s a) =
        globalCollapse (base (alphaCode s a)) 0
          (interpretation (contextCode s) (Lambda.deltaCode a)) ∧
      interpretation (contextCode s) a < denote (alphaCode s a) (deltaEnclosureTerm s a) := by
  have hc := Lambda.argument_accepted s a ha
  have hp := (Decomposition.parts_checked (contextCode s) 0 (Lambda.argumentCode a) hc).1
  have hn := (Decomposition.parts_normal (contextCode s) 0 (Lambda.argumentCode a) hc).1
  have hr := Lambda.delta_restricted s a ha
  have ht := unshifted_theta_checked s a 0 ha (deltaTerm a) (delta_theta_checked s a ha) hr
  have hnt := unshifted_normal s a ha (deltaTerm a) hp hn hr
  have hv : denote (alphaCode s a) (unshifted s a (deltaTerm a)) =
      interpretation (contextCode s) (Lambda.deltaCode a) := by
    simpa only [Lambda.deltaCode, Decomposition.highCode, interpretation_code, deltaTerm] using
      unshifted_value s a ha (deltaTerm a) hp hr
  refine ⟨ht, hnt, ?_, ?_⟩
  · change globalCollapse (base (alphaCode s a)) 0
      (denote (alphaCode s a) (unshifted s a (deltaTerm a))) = _
    rw [hv]
  · rw [← alpha_base s a ha]
    exact (SourceChi.Arithmetic.proper_theta_zero_iff _ _ ht hnt).mpr
      (by rw [hv]; exact Lambda.delta_nonzero s a ha)

/-- Actual executing iota of the root's true ANF Delta is strictly below
the concrete alpha collapse at original Delta. The caller is derived from
the original high root, without an extra admission or support guard. -/
theorem literalDelta_lt_enclosure (s a : Nat) (ha : rootCheck s a = true) :
    interpretation (alphaCode s a) (literalCode s a (Lambda.deltaCode a)) <
      denote (alphaCode s a) (deltaEnclosureTerm s a) := by
  have hc := Lambda.argument_accepted s a ha
  have hn := (Decomposition.parts_normal (contextCode s) 0 (Lambda.argumentCode a) hc).1
  have hh := transform_argument_lt_theta s a 0 ha (deltaTerm a) (delta_theta_checked s a ha)
    hn (Lambda.delta_restricted s a ha)
  simpa only [literalCode, Lambda.delta_input s a ha, Bool.cond_true, Lambda.deltaCode,
    Decomposition.highCode, stateCode_code, interpretation_code, deltaTerm, deltaEnclosureTerm] using hh

/-- The executing epsilon lambda branch is bounded by the SAME concrete
target collapse. The printed alpha-plus identification remains separate. -/
theorem lambda_lt_enclosure (s a out : Nat) (ho : out ∈ Lambda.execute s a) :
    interpretation (alphaCode s a) out < denote (alphaCode s a) (deltaEnclosureTerm s a) := by
  have hs := Lambda.execute_spec s a out ho
  have ha : rootCheck s a = true := hs.1
  obtain ⟨d, hd⟩ := SourceZeta.zeta_returns s a (Bool.and_eq_true.mp ha).1
  have hz := SourceZeta.zeta_spec s a d hd
  have hp := checked_theta_pos_principal (alphaCode s a) 0 (unshifted s a (deltaTerm a))
    (delta_enclosure_spec s a ha).1
  rw [hs.2.2]
  exact hp.2 (literalDelta_lt_enclosure s a ha)
    (hz.2.2.2.1.symm.trans_lt (hz.2.2.2.2.trans (delta_enclosure_spec s a ha).2.2.2))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Iota.Enclosure
