import Alexander313.Wilken.HereditaryThetaSupport

/-!
# Actual principal representatives after opening hereditary parameters

An outer parameter at a positive level decodes its actual earlier tree,
opens that tree's principal atoms recursively, and individually rewraps their
literal codes as parameters at the present level. Written sums concatenate
these atoms; theta nodes remain whole. Decoder failure yields an empty list,
but actual old admission excludes that branch in every fidelity theorem.

For the full admitted recursively normal grammar, the resulting list has
exactly the genuine canonical ANF values. Every returned representative is
itself admitted and recursively normal. In particular an earlier payload that
denotes a sum is flattened without losing its ordinal meaning. No ordinal
comparison, normalization, coverage or effectivity oracle is an input.
This does not yet construct normalization or comparison on all raw admitted
codes. All proof terms remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Theta

private def outerAtoms (openParameter : Nat → List (RelativeTerm Nat)) :
    RelativeTerm Nat → List (RelativeTerm Nat)
  | .parameter p => openParameter p
  | .sum a b => outerAtoms openParameter a ++ outerAtoms openParameter b
  | .theta k a => [.theta k a]

def atoms : Nat → RelativeTerm Nat → List (RelativeTerm Nat)
  | 0, t => thetaAtoms t
  | r + 1, t => outerAtoms (fun p =>
      ((decode p).map (fun u => (atoms r u).map (fun a => .parameter a.code))).getD []) t

@[simp] theorem atoms_parameter_zero (p : Nat) : atoms 0 (.parameter p) = [] := rfl

@[simp] theorem atoms_parameter_succ_code (r : Nat) (u : RelativeTerm Nat) :
    atoms (r + 1) (.parameter u.code) =
      (atoms r u).map (fun a => .parameter a.code) := by
  simp only [atoms, outerAtoms, decode_code, Option.map_some, Option.getD_some]

@[simp] theorem atoms_sum (r : Nat) (a b : RelativeTerm Nat) :
    atoms r (.sum a b) = atoms r a ++ atoms r b := by
  cases r <;> rfl

@[simp] theorem atoms_theta (r k : Nat) (a : RelativeTerm Nat) :
    atoms r (.theta k a) = [.theta k a] := by
  cases r <;> rfl

private theorem parameter_admissible (r n p : Nat) (hp : parameterCheck r p = true) :
    admissible r n (.parameter p) :=
  ⟨hp, .parameter (by simpa only [omegaSequence_zero] using parameter_sound r p hp)⟩

private theorem low_of_checked_value (r : Nat) (a : RelativeTerm Nat)
    (ha : check r a = true) (hvalue : denote r a < finiteBase (r + 1)) :
    lowCheck r a = true := by
  have hsort : a.outerSort ≤ 1 :=
    (denote_lt_iff_outerSort_le r a ha 1 (Nat.zero_lt_succ 0)).mp
      (hvalue.trans (finiteBase_lt_cardinal r))
  simp only [lowCheck, ha, hsort, decide_true, Bool.true_and]

/-- The representatives are constructed by literal recursive opening, while
their exact ANF and admission are proved from the unchanged source grammar. -/
theorem atoms_spec (r n : Nat) (t : RelativeTerm Nat)
    (ht : admissible r n t) (hn : Normal r t) :
    (∀ a ∈ atoms r t, admissible r n a ∧ Normal r a) ∧
      (atoms r t).map (finiteDenote r n) = canonicalANF (finiteDenote r n t) := by
  induction r using Nat.strong_induction_on generalizing n t with
  | h r ihr =>
    revert ht hn
    induction t with
    | parameter p =>
      intro ht hn
      cases r with
      | zero =>
        have hp0 : p = 0 := by
          simpa only [Payloads, parameterCheck_zero, beq_iff_eq] using ht.1
        subst p
        refine ⟨by simp [atoms_parameter_zero], ?_⟩
        simp [finiteDenote, eval, parameters_zero, SourceOne.parameters, canonicalANF_zero]
      | succ r =>
        have hp : lowCheckCode r p = true := ht.1
        obtain ⟨u, hu, hlow⟩ := (lowCheckCode_iff r p).mp hp
        subst p
        have hnu : Normal r u := by
          simpa only [normal_parameter_succ, decode_code, Option.getD_some] using hn
        let q := SourceOne.PublicCodes.fragment u
        have hucheck : check r u = true := (Bool.and_eq_true_iff.mp hlow).1
        have huad : admissible r q u := (finiteCheck_iff r q u).mp hucheck
        have hprev := ihr r (Nat.lt_succ_self r) q u huad hnu
        have hulow : denote r u < finiteBase (r + 1) :=
          (lt_nextBase_iff_checked r _).mpr ⟨u, hlow, rfl⟩
        have retained (a : RelativeTerm Nat) (ha : a ∈ atoms r u) :
            lowCheck r a = true ∧ Normal r a := by
          have haa := hprev.1 a ha
          have hamem : finiteDenote r q a ∈ canonicalANF (finiteDenote r q u) := by
            rw [← hprev.2]
            exact List.mem_map.mpr ⟨a, ha, rfl⟩
          have habound := canonicalANF_mem_le hamem
          rw [← denote_eq_finite r q a haa.1.2, ← denote_eq_finite r q u huad.2] at habound
          have hac : check r a = true :=
            (check_iff_finite_admissible r a).mpr ⟨q, haa.1⟩
          exact ⟨low_of_checked_value r a hac (habound.trans_lt hulow), haa.2⟩
        refine ⟨?_, ?_⟩
        · intro a ha
          rw [atoms_parameter_succ_code] at ha
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
          have hret := retained b hb
          refine ⟨parameter_admissible (r + 1) n b.code ?_, ?_⟩
          · simpa only [parameterCheck_succ, lowCheckCode_code] using hret.1
          · simpa only [normal_parameter_succ, decode_code, Option.getD_some] using hret.2
        · rw [atoms_parameter_succ_code, List.map_map]
          change (atoms r u).map (fun a => finiteDenote (r + 1) n (.parameter a.code)) =
            canonicalANF (interpretation r u.code)
          have hmap : (atoms r u).map (fun a => finiteDenote (r + 1) n (.parameter a.code)) =
              (atoms r u).map (finiteDenote r q) := by
            apply List.map_congr_left
            intro a ha
            change interpretation r a.code = finiteDenote r q a
            rw [interpretation_code]
            exact denote_eq_finite r q a (hprev.1 a ha).1.2
          rw [hmap, hprev.2, interpretation_code, denote_eq_finite r q u huad.2]
    | sum a b iha ihb =>
      intro ht hn
      cases ht.2 with
      | sum ha hb =>
        have hasa := iha ⟨ht.1.1, ha⟩ hn.sum_left
        have hasb := ihb ⟨ht.1.2, hb⟩ hn.sum_right
        refine ⟨?_, ?_⟩
        · intro p hp
          rw [atoms_sum] at hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hasa.1 p hp
          · exact hasb.1 p hp
        · rw [atoms_sum, List.map_append, hasa.2, hasb.2]
          exact (NormalSums.sum_anf
            ((normalSums_iff_global r n (.sum a b) (.sum ha hb)).mpr hn.«local»)).symm
    | theta k a ih =>
      intro ht hn
      refine ⟨?_, ?_⟩
      · intro b hb
        have he : b = .theta k a := by simpa only [atoms_theta, List.mem_singleton] using hb
        subst b
        exact ⟨ht, hn⟩
      · have hp := theta_pos_principal r n k a ht
        rw [canonicalANF_principal hp.1 hp.2]
        simp only [atoms_theta, List.map_singleton]

theorem atoms_admissible (r n : Nat) (t a : RelativeTerm Nat)
    (ht : admissible r n t) (hn : Normal r t) (ha : a ∈ atoms r t) :
    admissible r n a := ((atoms_spec r n t ht hn).1 a ha).1

theorem atoms_normal (r n : Nat) (t a : RelativeTerm Nat)
    (ht : admissible r n t) (hn : Normal r t) (ha : a ∈ atoms r t) :
    Normal r a := ((atoms_spec r n t ht hn).1 a ha).2

theorem atoms_denote_anf (r n : Nat) (t : RelativeTerm Nat)
    (ht : admissible r n t) (hn : Normal r t) :
    (atoms r t).map (denote r) = canonicalANF (denote r t) := by
  have hs := atoms_spec r n t ht hn
  have hmap : (atoms r t).map (denote r) = (atoms r t).map (finiteDenote r n) := by
    apply List.map_congr_left
    intro a ha
    exact denote_eq_finite r n a (hs.1 a ha).1.2
  rw [hmap, hs.2, denote_eq_finite r n t ht.2]

theorem atoms_denote_normal (r n : Nat) (t : RelativeTerm Nat)
    (ht : admissible r n t) (hn : Normal r t) :
    IsAdditiveNormalForm ((atoms r t).map (denote r)) := by
  rw [atoms_denote_anf r n t ht hn]
  exact canonicalANF_normal _

theorem atoms_denote_sum (r n : Nat) (t : RelativeTerm Nat)
    (ht : admissible r n t) (hn : Normal r t) :
    principalSum ((atoms r t).map (denote r)) = denote r t := by
  rw [atoms_denote_anf r n t ht hn, principalSum_canonicalANF]

/-- Every opened atom is a real earlier-level low code whenever its parent
has a low value. This licenses using its literal code as a later parameter. -/
theorem atoms_low (r n : Nat) (t a : RelativeTerm Nat)
    (ht : admissible r n t) (hn : Normal r t) (ha : a ∈ atoms r t)
    (hlow : denote r t < finiteBase (r + 1)) : lowCheck r a = true := by
  have had := atoms_admissible r n t a ht hn ha
  have hac : check r a = true := (check_iff_finite_admissible r a).mpr ⟨n, had⟩
  have hamem : denote r a ∈ canonicalANF (denote r t) := by
    rw [← atoms_denote_anf r n t ht hn]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  exact low_of_checked_value r a hac ((canonicalANF_mem_le hamem).trans_lt hlow)

end Alexander313.Wilken.RelativeTerm.Hereditary.Theta
