import Alexander313.Wilken.HereditaryNativeRhoPowerBoundSupport

/-!
# Actual rho bounds below the corrected omega-power producer

Real logarithm execution, genuine final-principal bounds and actual
finite chi correction establish the ordinary and strengthened bounds.
The strengthening derives the false log indicator from the original
query's actual indicator. Only real producer/graph and ordinal comparison
hypotheses are supplied. Source candidates only, uncompiled drafts.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho.Uniform.PowerBound

open PowerBoundSupport

theorem power_log_le (q b ell : Nat) (hl : ell ∈ LogEnd.execute q b)
    (hz : interpretation q b ≠ 0) :
    Ordinal.omega0 ^ interpretation q ell ≤ interpretation q b := by
  have hs := LogEnd.execute_spec q b ell hl
  have hn := Normalization.normalizeCode_accepted q b (HeightBoundary.input_spec q b hs.1).1
  have he := LogEnd.Support.endCode_spec q _ (LogEnd.normalized_low q b hs.1) hn.1
    (by simpa only [hn.2] using hz)
  have hp : Ordinal.omega0 ^ interpretation q ell =
      interpretation q (LogEndZero.endCode (Normalization.normalizeCode q b)) := by
    rw [LogEndZero.endCode_value q _ hn.1, hn.2]
    simpa only [Hereditary.LogEnd.SourceLogSpec, if_neg hz] using hs.2.2.2
  exact hp.le.trans (by simpa only [hn.2] using he.2.2.2.2.1)

theorem log_le_of_le_power (q b ell : Nat) (L : Ordinal.{0})
    (hl : ell ∈ LogEnd.execute q b)
    (hb : interpretation q b ≤ Ordinal.omega0 ^ L) : interpretation q ell ≤ L := by
  by_cases hz : interpretation q b = 0
  · have hs := (LogEnd.execute_spec q b ell hl).2.2.2
    have he : interpretation q ell = 0 := by
      simpa only [Hereditary.LogEnd.SourceLogSpec, hz, if_pos rfl] using hs
    rw [he]
    exact bot_le
  · apply le_of_not_gt
    intro h
    exact (omegaPower_strictMono h).not_ge ((power_log_le q b ell hl hz).trans hb)

theorem log_lt_of_lt_power (q b ell : Nat) (L : Ordinal.{0})
    (hl : ell ∈ LogEnd.execute q b) (hL : 0 < L)
    (hb : interpretation q b < Ordinal.omega0 ^ L) : interpretation q ell < L := by
  by_cases hz : interpretation q b = 0
  · have hs := (LogEnd.execute_spec q b ell hl).2.2.2
    have he : interpretation q ell = 0 := by
      simpa only [Hereditary.LogEnd.SourceLogSpec, hz, if_pos rfl] using hs
    rw [he]
    exact hL
  · apply lt_of_not_ge
    intro h
    exact ((power_log_le q b ell hl hz).trans_lt hb).not_ge
      (omegaPower_strictMono.monotone h)

/-- Every actual rho query below the real corrected-power value satisfies
the divided-head product bound, with no log/correction oracle. -/
theorem rho_le_corrected_power (q c k b out : Nat)
    (hc : lowCheckCode q c = true) (hn : Comparison.acceptedCode q c = true)
    (hlim : interpretation q c = 0 ∨ IsSuccLimit (interpretation q c))
    (ho : out ∈ execute q b)
    (hb : interpretation q b ≤ Ordinal.omega0 ^
      (interpretation q c + cond (SourceChi.chiCode q c) (1 : Ordinal.{0}) 0 +
        (k : Ordinal.{0}))) :
    interpretation q out ≤ base q * (interpretation q c + (k : Ordinal.{0})) := by
  obtain ⟨ell, hl, hm⟩ := Part.mem_bind_iff.mp ho
  have hs := LogEnd.execute_spec q b ell hl
  have hlog := log_le_of_le_power q b ell _ hl hb
  rw [execute_formula q b out ell ho hl]
  exact mul_le_mul_right (corrected_index_le q c k ell hn hs.2.1 hlim hlog) _

/-- The actual false query indicator gives the stronger successor bound.
The product coefficient must be positive, as derived by real high roots
in the source adapters; that arithmetic premise is explicit here. -/
theorem rho_add_base_le_corrected_power (q c k b out : Nat)
    (hc : lowCheckCode q c = true) (hn : Comparison.acceptedCode q c = true)
    (hlim : interpretation q c = 0 ∨ IsSuccLimit (interpretation q c))
    (hA : 0 < interpretation q c + (k : Ordinal.{0}))
    (hbnormal : Comparison.acceptedCode q b = true)
    (hχ : SourceChi.chiCode q b = false) (ho : out ∈ execute q b)
    (hb : interpretation q b < Ordinal.omega0 ^
      (interpretation q c + cond (SourceChi.chiCode q c) (1 : Ordinal.{0}) 0 +
        (k : Ordinal.{0}))) :
    interpretation q out + base q ≤ base q * (interpretation q c + (k : Ordinal.{0})) := by
  by_cases hz : interpretation q b = 0
  · rw [execute_zero q b out ho hz, zero_add]
    simpa only [mul_one] using mul_le_mul_right (Order.one_le_iff_pos.mpr hA) (base q)
  · obtain ⟨ell, hl, hm⟩ := Part.mem_bind_iff.mp ho
    have hs := LogEnd.execute_spec q b ell hl
    have hL : 0 < interpretation q c +
        cond (SourceChi.chiCode q c) (1 : Ordinal.{0}) 0 + (k : Ordinal.{0}) := by
      cases h : SourceChi.chiCode q c with
      | false => simpa only [h, Bool.cond_false, add_zero] using hA
      | true =>
        simp only [h, Bool.cond_true, finite_one_swap]
        exact hA.trans_le le_self_add
    have hlog := log_lt_of_lt_power q b ell _ hl hL hb
    have hχlog : SourceChi.chiCode q ell = false :=
      (SourceChi.LogEndUniform.chiCode_logend q b ell hs.1 hbnormal hl).trans hχ
    have hindex := corrected_index_succ_le q c k ell hn hs.2.1 hs.2.2.1 hlim hχlog hlog
    calc
      interpretation q out + base q = base q *
          (OrdinalRightSubtraction.rightSubtract (interpretation q ell)
            (chiNat q ell : Ordinal.{0}) + 1) := by
        rw [execute_formula q b out ell ho hl, mul_add, mul_one]
      _ ≤ base q * (interpretation q c + (k : Ordinal.{0})) := mul_le_mul_right hindex _

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceRho.Uniform.PowerBound
