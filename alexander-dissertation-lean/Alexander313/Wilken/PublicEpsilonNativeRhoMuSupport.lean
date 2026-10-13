import Alexander313.Wilken.PublicEpsilonNativeMappedOmegaQuotient
import Alexander313.Wilken.PublicEpsilonNativeMu
import Alexander313.Wilken.HereditaryNativeRhoMu

/-!
# Genuine zero-or-limit mapped coefficient at every original public epsilon

The original Normal ANF has no unit atoms when its value is zero or a
proper limit. Actual generic iota preserves the LOW unit and reflects its
order on every original restricted atom. This derives the mapped coefficient
limit condition needed by real rho cancellation; it is not a supplied
coefficient or limit oracle. Original selected-root scope is retained.
These source-only proof candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.RhoMuSupport

open ThetaCourse OrderSupport

private theorem normal_atoms_nonunit (q : Nat) (t : RelativeTerm Nat)
    (ht : check q t = true) (hn : Comparison.Normal q t)
    (hl : denote q t = 0 ∨ IsSuccLimit (denote q t)) (x : RelativeTerm Nat)
    (hx : x ∈ Comparison.atoms t) : denote q x ≠ 1 := by
  intro he
  have hc : checkCode q t.code = true := by simpa only [checkCode_code] using ht
  have hz : FiniteTailDecomposition.offset q t.code = 0 :=
    SourceRho.Uniform.MuSupport.offset_zero_of_limit q t.code hc
      (by simpa only [interpretation_code] using hl)
  have hempty : NativeContext.OmegaQuotient.selectUnits true q
      (Arithmetic.normalizedWord q t.code) = [] := List.eq_nil_of_length_eq_zero hz
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
  have hunit := (NativeContext.OmegaQuotient.unitTest_exact q (Bool.and_eq_true.mp ht).1
    u hus.1 hus.2.1).mpr huv
  have hsel := (NativeContext.OmegaQuotient.selectUnits_mem true q _ u).mpr ⟨hu, hunit⟩
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

/-- Actual original ANF and genuine generic unit-order reflection derive
zero-or-proper-limit preservation on the complete restricted source domain. -/
theorem transform_zero_or_limit (q root : Nat) (ha : rootCheck q root = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : Restricted q root t)
    (hl : denote q t = 0 ∨ IsSuccLimit (denote q t)) :
    denote (betaCode q root) (transform q root t) = 0 ∨
      IsSuccLimit (denote (betaCode q root) (transform q root t)) := by
  let u : RelativeTerm Nat := rawTree LogEndZero.unitCode
  have hu := Decomposition.input_tree q _
    (LogEndZero.unitCode_accepted q (source_checked q root ha))
  have hur : Restricted q root u := by
    intro x hx
    simp only [u, LogEndZero.unitCode, rawTree_code, Restricted, Iota.fullList,
      RelativeTerm.PrincipalSupport.principalList, List.not_mem_nil] at hx
  have huv : denote q u = 1 := by
    rw [← Decomposition.input_value q _
      (LogEndZero.unitCode_accepted q (source_checked q root ha))]
    exact LogEndZero.unitCode_value q
  have hut : denote (betaCode q root) (transform q root u) = 1 :=
    (transform_low_value q root ha u hu.1 hur (by
      simp only [u, LogEndZero.unitCode, rawTree_code, outerSort]; omega)).trans huv
  rw [← mapped_atoms_value q root ha t ht hn hr]
  apply principalSum_limit_zero
  intro p hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  have hxs := Iota.OrderInduction.atoms_checked_normal q t x ht hn hx
  have hxr := restricted_atoms q root t x hr hx
  have hnormal := transform_atoms_anf q root ha t ht hn hr
  have hprincipal := (canonicalANF_normal
    (denote (betaCode q root) (transform q root t))).1 _ (by
      rw [← hnormal]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩)
  refine ⟨?_, hprincipal.2⟩
  rw [← hut]
  apply (transform_lt_iff q root ha u x hu.1 hxs.1 hu.2 hxs.2 hur hxr).mpr
  rw [huv]
  have hsource := (Iota.OrderInduction.source_atoms_normal q t ht hn).1 _
    (List.mem_map.mpr ⟨x, hx, rfl⟩)
  exact lt_of_le_of_ne (Order.one_le_iff_pos.mpr hsource.1)
    (normal_atoms_nonunit q t ht hn hl x hx).symm

/-- The unchanged original generic mu root alone derives the genuine
mapped coefficient zero-or-proper-limit status. -/
theorem mappedCoefficient_zero_or_limit (q root : Nat) (ha : Mu.inputCheck q root = true) :
    interpretation (betaCode q root) (Mu.mappedCoefficient q root) = 0 ∨
      IsSuccLimit (interpretation (betaCode q root) (Mu.mappedCoefficient q root)) := by
  have hs := OmegaQuotient.coefficientCode_spec q root ha
  obtain ⟨_, t, hcode, ht, hn, hstar⟩ := (inputCheck_exact q root _).mp hs.2.1
  have hr := (restricted_iff_sourceStar q root ha t ht hn).mpr hstar
  have hl : denote q t = 0 ∨ IsSuccLimit (denote q t) := by
    simpa only [hcode, interpretation_code] using hs.2.2.1
  have hv := transform_zero_or_limit q root ha t ht hn hr hl
  have hout : Mu.mappedCoefficient q root = (transform q root t).code := by
    rw [Mu.mappedCoefficient, hcode, literalCode_code q root ha t ht hn hr]
  simpa only [hout, interpretation_code] using hv

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonIota.RhoMuSupport
