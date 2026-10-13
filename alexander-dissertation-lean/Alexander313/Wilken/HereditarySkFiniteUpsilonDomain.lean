import Alexander313.Wilken.FiniteUpsilonDomain
import Alexander313.Wilken.HereditarySkPublicDictionary

/-!
# Exact finite upsilon exclusion of the selected public sk producer

The actual zero-started finite upsilon sequence is already constructed
independently from the original global source grammar. Its positive terms
agree with finiteBase. The genuine least endpoint scan therefore detects
exactly this finite image on its original canonical epsilon domain. This
identifies the executing dictionary guard with finite upsilon exclusion;
it does not construct or classify a transfinite upsilon segment, or identify
mu across arbitrary selected source contexts. Uncompiled source candidate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicDictionary.FiniteDomain

/-- The image of the actually constructed zero-started finite sequence. -/
def FiniteUpsilonImage (xi : Ordinal.{0}) : Prop :=
  ∃ n : Nat, xi = sourceUpsilonFinite n

/-- The stored public level need not be minimal. The real endpoint scan,
lower bound and upper bound force the true level of each finite base. -/
theorem level_eq_of_finiteBase (gamma n : Nat)
    (hg : PublicEpsilonSourceDictionary.inputCheck gamma = true)
    (hv : unionInterpretation gamma = finiteBase (n + 1)) :
    PublicEpsilonSourceDictionary.level gamma = n + 1 := by
  have hc := ((PublicEpsilonSourceDictionary.inputCheck_exact gamma).mp hg).1
  have hl := PublicEpsilonSourceDictionary.level_lower gamma hg
  have hu := (PublicEpsilonSourceDictionary.level_bound gamma hc).2.1
  rw [hv] at hl hu
  have hlo := finiteBase_strictMono.le_iff_le.mp hl
  have hhi := finiteBase_strictMono.lt_iff_lt.mp hu
  omega

/-- A base point is exactly a finite upsilon value, including the actual
zero-start convention and excluding its zero endpoint by epsilon positivity. -/
theorem basePoint_true_iff_finite (gamma : Nat)
    (hg : PublicEpsilonSourceDictionary.inputCheck gamma = true) :
    PublicEpsilonSourceDictionary.basePoint gamma = true ↔ FiniteUpsilonImage (unionInterpretation gamma) := by
  have hc := ((PublicEpsilonSourceDictionary.inputCheck_exact gamma).mp hg).1
  constructor
  · intro hb
    have hl := (PublicEpsilonSourceDictionary.base_point_spec gamma hg hb).1
    have hv := (PublicEpsilonSourceDictionary.basePoint_exact gamma hc).mp hb
    cases he : PublicEpsilonSourceDictionary.level gamma with
    | zero => exact False.elim (by omega)
    | succ n =>
      refine ⟨n + 1, ?_⟩
      have hv' : unionInterpretation gamma = finiteBase (n + 1) := by
        simpa only [he] using hv
      exact hv'.trans (sourceUpsilonFinite_eq_finiteBase_succ n).symm
  · rintro ⟨n, hv⟩
    cases n with
    | zero =>
      have hpos : 0 < unionInterpretation gamma := zero_lt_one.trans
        (EpsilonOffsets.epsilon_one_lt ((PublicEpsilonSourceDictionary.inputCheck_exact gamma).mp hg).2)
      have hz : unionInterpretation gamma = 0 := hv.trans sourceUpsilonFinite_zero
      rw [hz] at hpos
      exact False.elim ((lt_irrefl (0 : Ordinal.{0})) hpos)
    | succ n =>
      have hb := hv.trans (sourceUpsilonFinite_eq_finiteBase_succ n)
      have hl := level_eq_of_finiteBase gamma n hg hb
      apply (PublicEpsilonSourceDictionary.basePoint_exact gamma hc).mpr
      simpa only [hl] using hb

theorem basePoint_false_iff_not_finite (gamma : Nat)
    (hg : PublicEpsilonSourceDictionary.inputCheck gamma = true) :
    PublicEpsilonSourceDictionary.basePoint gamma = false ↔ ¬ FiniteUpsilonImage (unionInterpretation gamma) := by
  constructor
  · intro hb hf
    have ht := (basePoint_true_iff_finite gamma hg).mpr hf
    rw [hb] at ht
    cases ht
  · intro hn
    cases hb : PublicEpsilonSourceDictionary.basePoint gamma with
    | false => rfl
    | true => exact False.elim (hn ((basePoint_true_iff_finite gamma hg).mp hb))

/-- Every original canonical public epsilon lies in the actual omega
supremum of the constructed finite sequence. -/
theorem below_sourceUpsilonOmega (gamma : Nat)
    (hg : PublicEpsilonSourceDictionary.inputCheck gamma = true) :
    unionInterpretation gamma < sourceUpsilonOmega := by
  have hb := (PublicEpsilonSourceDictionary.level_bound gamma ((PublicEpsilonSourceDictionary.inputCheck_exact gamma).mp hg).1).2.1
  have ht : finiteBase (PublicEpsilonSourceDictionary.level gamma + 1) < sourceUpsilonOmega := by
    rw [← sourceUpsilonFinite_eq_finiteBase_succ]
    exact sourceUpsilonFinite_lt_omega _
  exact hb.trans ht

theorem inputCheck_exact (gamma cutoff : Nat) :
    Support.inputCheck gamma cutoff = true ↔
      Canonical.check gamma = true ∧
        Ordinal.omega0 ^ unionInterpretation gamma = unionInterpretation gamma ∧
          ¬ FiniteUpsilonImage (unionInterpretation gamma) ∧ unionCheck cutoff = true := by
  constructor
  · intro hi
    have hs := (Support.inputCheck_exact gamma cutoff).mp hi
    have he := (PublicEpsilonSourceDictionary.inputCheck_exact gamma).mp hs.1
    exact ⟨he.1, he.2, (basePoint_false_iff_not_finite gamma hs.1).mp hs.2.1, hs.2.2⟩
  · rintro ⟨hc, he, hn, hcut⟩
    have hg := (PublicEpsilonSourceDictionary.inputCheck_exact gamma).mpr ⟨hc, he⟩
    exact (Support.inputCheck_exact gamma cutoff).mpr
      ⟨hg, (basePoint_false_iff_not_finite gamma hg).mpr hn, hcut⟩

/-- Exact executing domain with genuine finite upsilon exclusion. The
global transfinite image and arbitrary cross-source mu are not assumed. -/
theorem execute_domain (gamma cutoff : Nat) :
    (SkPublicDictionary.execute (gamma, cutoff)).Dom ↔
      Canonical.check gamma = true ∧
        Ordinal.omega0 ^ unionInterpretation gamma = unionInterpretation gamma ∧
          ¬ FiniteUpsilonImage (unionInterpretation gamma) ∧ unionCheck cutoff = true :=
  (SkPublicDictionary.execute_domain gamma cutoff).trans (inputCheck_exact gamma cutoff)

end Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicDictionary.FiniteDomain
