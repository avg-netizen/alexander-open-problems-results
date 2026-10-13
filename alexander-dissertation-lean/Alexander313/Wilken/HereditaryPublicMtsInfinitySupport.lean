import Alexander313.Wilken.HereditaryPublicMts
import Alexander313.Wilken.HereditaryGlobalHSmallSupport
import Alexander313.Wilken.SourceOneUnboundedPublicReturn
import Alexander313.Wilken.PublicEpsilonNativeContextReturnSupport

/-!
# The genuine full alpha-infinity boundary and independent mu callers

Unconditional SAME-value LOW returns into the ORIGINAL selected dictionary
prove the reverse boundary inclusion. Genuine finite-boundary monotonicity
supplies the other inclusion. Hence the actual grammar at a proper canonical
epsilon gamma has the real next finite upsilon endpoint as its boundary,
without restricting its inputs to OWN alpha-plus. Every HIGH node in that
whole grammar lies in the same proper finite gap, deriving its independent
public mu query. No incoming-context mu identity outside OWN is asserted.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.InfinitySupport

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota

/-- The unconditional actual SAME-value return proves the reverse inclusion
for the WHOLE LOW grammar of any genuine original positive-context root. -/
theorem native_boundary_le (q alpha : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true) :
    globalBoundary (base (betaCode q alpha)) 0 ≤ globalBoundary (base q) 0 := by
  apply le_of_not_gt
  intro hlt
  obtain ⟨t, ht, hv⟩ := (lt_boundary_iff_checked (betaCode q alpha)
    (betaCode_baseCheck q alpha ha) (globalBoundary (base q) 0)).mp hlt
  have hs := Bool.and_eq_true.mp ht
  have hl := ContextTranslation.ReturnSupport.returnedCode_low q alpha ha t hs.1
    (of_decide_eq_true hs.2)
  have hr := ContextTranslation.ReturnSupport.returnedCode_spec q alpha ha t hs.1
  have hb := checked_low_bound q _ hl
  rw [hr.2, hv] at hb
  exact (lt_irrefl _ hb)

/-- Real boundary monotonicity and the actual unrestricted return give
equality of the original and raised-root LOW grammar boundaries. -/
theorem native_boundary_eq (q alpha : Nat)
    (ha : RootLowCollapse.rootCheck q alpha = true) :
    globalBoundary (base (betaCode q alpha)) 0 = globalBoundary (base q) 0 := by
  apply le_antisymm (native_boundary_le q alpha ha)
  rw [beta_base q alpha ha]
  exact SourceAdditiveTracking.ReplacementSupport.globalBoundary_mono_base _ _
    (base_pos q (RootLowCollapse.source_checked q alpha ha))
    (RootLowCollapse.root_base_le q alpha ha) (RootLowCollapse.root_lt_first q alpha ha)

/-- ORIGINAL check0 LOW return excludes a value at the first source-one
boundary from the whole raised alpha grammar, with no Native-base-one parser. -/
theorem source_one_boundary_le (alpha : Nat)
    (ha : SourceOneIota.rootCheck alpha = true) :
    globalBoundary (base (SourceOneIota.alphaCode alpha)) 0 ≤ finiteBase 1 := by
  apply le_of_not_gt
  intro hlt
  obtain ⟨c, hc, hv⟩ := (lt_boundary_iff_code (SourceOneIota.alphaCode alpha)
    (SourceOneIota.alphaCode_baseCheck alpha ha) (finiteBase 1)).mp hlt
  have hl := SourceOneIota.UnboundedPublicReturn.sourceTermCode_low alpha c ha hc
  have hr := SourceOneIota.UnboundedPublicReturn.sourceTermCode_spec alpha c ha
    (Bool.and_eq_true.mp hc).1
  have hb : Hereditary.interpretation 0 (SourceOneIota.UnboundedPublicReturn.sourceTermCode alpha c) <
      finiteBase 1 := (lt_nextBase_iff_code 0 _).mpr ⟨_, hl, rfl⟩
  rw [hr.2, hv] at hb
  exact (lt_irrefl _ hb)

theorem source_one_boundary_eq (alpha : Nat)
    (ha : SourceOneIota.rootCheck alpha = true) :
    globalBoundary (base (SourceOneIota.alphaCode alpha)) 0 = finiteBase 1 := by
  apply le_antisymm (source_one_boundary_le alpha ha)
  rw [SourceOneIota.OrderSupport.alpha_base alpha ha, finiteBase_succ, finiteBase_zero]
  exact SourceAdditiveTracking.ReplacementSupport.globalBoundary_mono_base _ _ zero_lt_one
    (EpsilonOffsets.epsilon_one_lt (SourceOneIota.root_epsilon alpha ha)).le
    (SourceOneIota.root_lt_first alpha ha)

/-- The literal canonical gamma has exactly its genuine finite source
upper endpoint as alpha-infinity, for BOTH original source dictionaries. -/
theorem public_boundary_eq (gamma : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true) :
    globalBoundary (base gamma) 0 = finiteBase (PublicEpsilonSourceDictionary.level gamma + 1) := by
  cases hl : PublicEpsilonSourceDictionary.level gamma with
  | zero =>
    have ha := ContextSupport.source_one_base gamma hg hl
    simpa only [ha.2, hl, Nat.zero_add] using
      source_one_boundary_eq (PublicEpsilonSourceDictionary.sourceRootCode gamma) ha.1
  | succ s =>
    have hn : PublicEpsilonSourceDictionary.level gamma ≠ 0 := by omega
    have ha := ContextSupport.positive_base gamma hg hn
    have he := native_boundary_eq (MuPublicDictionary.Support.nativeContext gamma)
      (MuPublicDictionary.Support.nativeRoot gamma) ha.1
    have hb : base (MuPublicDictionary.Support.nativeContext gamma) = finiteBase (s + 1) := by
      simp only [MuPublicDictionary.Support.nativeContext, PublicEpsilonSourceDictionary.sourceIndex,
        hl, Nat.add_sub_cancel, NativePublicBridge.contextCode_value]
    simpa only [ha.2, hb, hl, finiteBase_succ] using he

def infinityCode (gamma : Nat) : Nat :=
  PublicEpsilonSourceDictionary.endpointCode (PublicEpsilonSourceDictionary.level gamma + 1)

theorem infinityCode_primrec : Primrec infinityCode :=
  PublicEpsilonSourceDictionary.endpointCode_primrec.comp
    (Primrec.succ.comp PublicEpsilonSourceDictionary.level_primrec)

theorem infinityCode_spec (gamma : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true) :
    Canonical.check (infinityCode gamma) = true ∧
      unionInterpretation (infinityCode gamma) = globalBoundary (base gamma) 0 :=
  ⟨PublicEpsilonSourceDictionary.endpointCode_checked _,
    (PublicEpsilonSourceDictionary.endpointCode_value _).trans (public_boundary_eq gamma hg).symm⟩

/-- A real HIGH node anywhere below the full gamma grammar boundary lies
in the original selected finite gap; this supplies its public mu domain
without any incoming-context mu identification or OWN premise. -/
theorem high_public_caller (gamma c : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hc : Mu.inputCheck gamma c = true) :
    MuPublicDictionary.Support.inputCheck (UniformPublicReturn.publicCode gamma c) = true := by
  have hp := UniformPublicReturn.publicCode_spec gamma c
    ((UniformPublicReturn.inputCheck_exact gamma c).mpr (root_low gamma c hc))
  have he : GlobalMuDictionary.Support.inputCheck (UniformPublicReturn.publicCode gamma c) = true :=
    (GlobalMuDictionary.Support.inputCheck_exact _).mpr
      ⟨hp.1, by rw [hp.2]; exact RootLowCollapse.root_epsilon gamma c hc⟩
  have hs := (MuPublicDictionary.Support.inputCheck_exact gamma).mp hg
  have hfloor := PublicEpsilonSourceDictionary.proper_lower gamma hs.1 hs.2
  have hroot := Mu.root_base_lt gamma c hc
  have hbound := checked_low_bound gamma c (root_low gamma c hc)
  rw [public_boundary_eq gamma hg] at hbound
  have hgap : GlobalTrackingSequences.TailGap (PublicEpsilonSourceDictionary.level gamma)
      [UniformPublicReturn.publicCode gamma c] := by
    change sourceUpsilon (PublicEpsilonSourceDictionary.level gamma : Ordinal.{0}) <
        unionInterpretation (UniformPublicReturn.publicCode gamma c) ∧
      unionInterpretation (UniformPublicReturn.publicCode gamma c) <
        sourceUpsilon ((PublicEpsilonSourceDictionary.level gamma + 1 : Nat) : Ordinal.{0})
    rw [PublicUpsilonSegment.successor_value, hp.2]
    refine ⟨?_, hbound⟩
    cases hl : PublicEpsilonSourceDictionary.level gamma with
    | zero =>
      rw [Nat.cast_zero, sourceUpsilon_zero]
      exact (base_pos gamma (RootLowCollapse.source_checked gamma c hc)).trans hroot
    | succ m =>
      simpa only [hl, PublicUpsilonSegment.successor_value] using hfloor.trans hroot
  exact GlobalTrackingSequences.SmallHSupport.proper_of_gap _ _ he hgap

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.InfinitySupport
