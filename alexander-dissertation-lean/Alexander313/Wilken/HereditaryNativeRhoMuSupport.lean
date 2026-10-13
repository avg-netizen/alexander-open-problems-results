import Alexander313.Wilken.HereditaryNativeSourceRhoUniform
import Alexander313.Wilken.HereditaryNativeMu
import Alexander313.Wilken.HereditaryNativeIotaOrderInduction

/-!
# Genuine logarithm and finite-tail cancellation for rho at mu

The actual native omega-power output has its original exponent as the
unique real last-log value. Genuine zero-or-limit finite-tail uniqueness
identifies the computed lambda; actual source chi invariance then cancels
the finite correction by dotted RIGHT subtraction. The original iota ANF
and unit order prove zero-or-limit preservation on the original restricted
domain. No logarithm, finite decomposition, coefficient or chi oracle.
These source-only proof candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho.Uniform.MuSupport

open ThetaCourse
open NativePublicBridge (contextCode contextCode_checked)

theorem rightSubtract_add_one (a : Ordinal.{0}) :
    OrdinalRightSubtraction.rightSubtract (a + 1) 1 = a := by
  by_cases hz : a = 0
  · subst a
    simpa only [zero_add] using OrdinalRightSubtraction.rightSubtract_of_le 1 1 le_rfl
  · have hp : 0 < a := bot_lt_iff_ne_bot.mpr hz
    have hab : (1 : Ordinal.{0}) < a + 1 := Order.lt_add_one_iff.mpr (Order.one_le_iff_pos.mpr hp)
    have hs := OrdinalRightSubtraction.rightSubtract_minimum (a + 1) 1 hab ⟨a, rfl⟩
    exact (Ordinal.add_right_cancel 1).mp (by simpa only [Nat.cast_one] using hs.1.symm)

theorem rightSubtract_finite_correction (a : Ordinal.{0}) (b : Bool) (k : Nat) :
    OrdinalRightSubtraction.rightSubtract (a + (cond b (1 : Ordinal.{0}) 0) + (k : Ordinal.{0}))
      (cond b (1 : Ordinal.{0}) 0) = a + (k : Ordinal.{0}) := by
  cases b with
  | false => simp only [Bool.cond_false, add_zero, OrdinalRightSubtraction.rightSubtract_zero_right]
  | true =>
    simp only [Bool.cond_true]
    have he : a + 1 + (k : Ordinal.{0}) = (a + (k : Ordinal.{0})) + 1 := by
      rw [add_assoc, ← Nat.cast_one, ← Nat.cast_add, Nat.add_comm 1 k, Nat.cast_add,
        Nat.cast_one, ← add_assoc]
    rw [he, rightSubtract_add_one]

/-- A genuine native omega-power output has its actual original exponent
as the real last-log value; positivity and principality are constructed. -/
theorem log_powerCode_value (q c ell : Nat) (hc : lowCheckCode q c = true)
    (hl : ell ∈ LogEnd.execute q (OmegaPowers.powerCode q c)) :
    interpretation q ell = interpretation q c := by
  have hp := OmegaPowers.powerCode_spec q c hc
  have hs := (LogEnd.execute_spec q _ ell hl).2.2.2
  have hpos : 0 < interpretation q (OmegaPowers.powerCode q c) := by
    rw [hp.2.2]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos
  have hprincipal : Ordinal.IsPrincipal (· + ·)
      (interpretation q (OmegaPowers.powerCode q c)) := by
    rw [hp.2.2]
    exact Ordinal.isPrincipal_add_omega0_opow _
  apply omegaPower_strictMono.injective
  have hv : Ordinal.omega0 ^ interpretation q ell =
      Hereditary.LogEnd.endValue (interpretation q (OmegaPowers.powerCode q c)) := by
    simpa only [Hereditary.LogEnd.SourceLogSpec, if_neg (ne_of_gt hpos)] using hs
  exact hv.trans ((SourceChi.Powers.endValue_principal _ hpos hprincipal).trans hp.2.2)

/-- Actual unit stripping of an originally admitted zero-or-limit value
has no finite tail. This is derived from genuine decomposition uniqueness. -/
theorem offset_zero_of_limit (q c : Nat) (hc : checkCode q c = true)
    (hl : interpretation q c = 0 ∨ IsSuccLimit (interpretation q c)) :
    FiniteTailDecomposition.offset q c = 0 := by
  have hs := FiniteTailDecomposition.lambdaCode_spec q c hc
  exact (LimitFiniteDecomposition.coefficient_unique _ _ _ 0 hs.2.1 hl
    (by simpa only [Nat.cast_zero, add_zero] using hs.2.2.symm)).2

private theorem normal_atoms_nonunit (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t)
    (hl : denote q t = 0 ∨ IsSuccLimit (denote q t)) (x : RelativeTerm Nat)
    (hx : x ∈ Comparison.atoms t) : denote q x ≠ 1 := by
  intro he
  have hc : checkCode q t.code = true := by simpa only [checkCode_code] using ht
  have hz : FiniteTailDecomposition.offset q t.code = 0 :=
    offset_zero_of_limit q t.code hc (by simpa only [interpretation_code] using hl)
  have hempty : OmegaQuotient.selectUnits true q (Arithmetic.normalizedWord q t.code) = [] :=
    List.eq_nil_of_length_eq_zero hz
  have hm : (1 : Ordinal.{0}) ∈ canonicalANF (denote q t) := by
    rw [← Iota.OrderInduction.source_atoms_anf q t ht hn]
    exact List.mem_map.mpr ⟨x, hx, he⟩
  have hword := Arithmetic.normalizedWord_spec q t.code hc
  have hm' : (1 : Ordinal.{0}) ∈
      (Arithmetic.normalizedWord q t.code).map (denote q) := by
    rw [hword.2, interpretation_code]
    exact hm
  obtain ⟨u, hu, huv⟩ := List.mem_map.mp hm'
  have hus := hword.1 u hu
  have hunit := (OmegaQuotient.unitTest_exact q (Bool.and_eq_true.mp ht).1 u hus.1 hus.2.1).mpr huv
  have hsel := (OmegaQuotient.selectUnits_mem true q _ u).mpr ⟨hu, hunit⟩
  simp only [hempty, List.not_mem_nil] at hsel

private theorem principalSum_limit_zero (as : List Ordinal.{0})
    (hs : ∀ p ∈ as, 1 < p ∧ Ordinal.IsPrincipal (· + ·) p) :
    principalSum as = 0 ∨ IsSuccLimit (principalSum as) := by
  revert hs
  induction as with
  | nil => intro hs; exact Or.inl rfl
  | cons p as ih =>
    intro hs
    have hp := hs p List.mem_cons_self
    rcases ih (fun q hq => hs q (List.mem_cons_of_mem _ hq)) with hz | hl
    · exact Or.inr (by simpa only [principalSum, hz, add_zero] using
        Ordinal.isSuccLimit_of_isPrincipal_add hp.1 hp.2)
    · exact Or.inr (Ordinal.isSuccLimit_add _ hl)

/-- Every original restricted zero-or-limit source term maps to zero or
a proper limit. Actual ANF and actual unit-order reflection derive this. -/
theorem transform_zero_or_limit (s a : Nat) (ha : Iota.rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hn : Comparison.Normal (contextCode s) t) (hr : Iota.Restricted s a t)
    (hl : denote (contextCode s) t = 0 ∨ IsSuccLimit (denote (contextCode s) t)) :
    denote (Iota.alphaCode s a) (Iota.transform s a t) = 0 ∨
      IsSuccLimit (denote (Iota.alphaCode s a) (Iota.transform s a t)) := by
  let u : RelativeTerm Nat := rawTree LogEndZero.unitCode
  have hu := Decomposition.input_tree (contextCode s) _
    (LogEndZero.unitCode_accepted _ (contextCode_checked s))
  have hur : Iota.Restricted s a u := by
    intro x hx
    simp only [u, LogEndZero.unitCode, rawTree_code, Iota.fullList,
      RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hx
  have huv : denote (contextCode s) u = 1 := by
    rw [← Decomposition.input_value _ _ (LogEndZero.unitCode_accepted _ (contextCode_checked s))]
    exact LogEndZero.unitCode_value _
  have hut : denote (Iota.alphaCode s a) (Iota.transform s a u) = 1 := by
    exact (Iota.transform_low_value s a ha u hu.1 hur (by simp only [u, LogEndZero.unitCode,
      rawTree_code, RelativeTerm.outerSort]; omega)).trans huv
  rw [← Iota.OrderInduction.mapped_atoms_value s a ha t ht hn hr]
  apply principalSum_limit_zero
  intro p hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  have hxs := Iota.OrderInduction.atoms_checked_normal _ t x ht hn hx
  have hxr := Iota.OrderInduction.restricted_atoms s a t x hr hx
  have hnormal := Iota.transform_atoms_anf s a ha t ht hn hr
  have hprincipal := (canonicalANF_normal
    (denote (Iota.alphaCode s a) (Iota.transform s a t))).1 _ (by
      rw [← hnormal]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩)
  refine ⟨?_, hprincipal.2⟩
  rw [← hut]
  apply (Iota.transform_lt_iff s a ha u x hu.1 hxs.1 hu.2 hxs.2 hur hxr).mpr
  rw [huv]
  have hsource := (Iota.OrderInduction.source_atoms_normal _ t ht hn).1 _
    (List.mem_map.mpr ⟨x, hx, rfl⟩)
  exact lt_of_le_of_ne (Order.one_le_iff_pos.mpr hsource.1) (normal_atoms_nonunit _ t ht hn hl x hx).symm

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho.Uniform.MuSupport
