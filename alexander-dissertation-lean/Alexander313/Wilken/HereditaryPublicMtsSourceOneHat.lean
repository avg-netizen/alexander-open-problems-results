import Alexander313.Wilken.HereditaryPublicMtsPositiveHat
import Alexander313.Wilken.SourceOneNativeGammaHatFirstEntry

/-!
# Actual selected source-one covering and its original semantic singleton cut

The genuine selected original check-zero root has literal alphaCode=gamma,
and independently executing public mu is its ORIGINAL source-one mu. Native
alpha-context M execution agrees with the real Node word in FIRST values.
The original source-one singleton-minimum criterion thus identifies actual
emitted covering below the semantic hat inside OWN. No Native-base-one
grammar, computed minimum, outside-cut reach or full alpha-infinity claim.
Source-only uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.SourceOneHat

open NativeContext
open FirstSupport
open CoveringSupport (Covering)

def value (gamma : Nat) (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma = 0) : Ordinal.{0} :=
  SourceOneIota.GammaHat.value (PublicEpsilonSourceDictionary.sourceRootCode gamma)
    (ContextSupport.source_one_base gamma hg hl).1

theorem source_one_muValue (gamma : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma = 0) :
    SkPublicRecurrence.muValue gamma =
      SourceOneIota.Mu.sourceValue (PublicEpsilonSourceDictionary.sourceRootCode gamma) := by
  have hz := beq_iff_eq.mpr hl
  simpa only [SkPublicRecurrence.muValue, (MuPublicDictionary.publicCode_spec gamma hg).2,
    MuPublicDictionary.Support.sourceValue, hz, Bool.cond_true]

/-- Original selected source-zero admission and literal alphaCode fidelity
turn the real alpha-context M criterion into the independent public FIRST cut. -/
theorem search_first_iff_lt_value (gamma beta d : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hl : PublicEpsilonSourceDictionary.level gamma = 0)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    firstValue gamma (nativeRoot gamma d) ≤ SkPublicRecurrence.muValue gamma ↔
      unionInterpretation beta < value gamma ((inputCheck_exact gamma beta).mp hi).1 hl := by
  have hg := ((inputCheck_exact gamma beta).mp hi).1
  have ha := ContextSupport.source_one_base gamma hg hl
  let root := PublicEpsilonSourceDictionary.sourceRootCode gamma
  let current := nativeRoot gamma d
  have hs := nativeRoot_spec gamma beta d hi hd
  have hn := (SourceLocalization.inputCheck_exact gamma current).mp hs.1
  have hfloor : base gamma ≤ interpretation gamma current := by
    rw [hs.2]
    exact ((inputCheck_exact gamma beta).mp hi).2.2.2.2.1
  have hmc : SourceMultiplicativePrincipal.inputCheck gamma current = true :=
    (SourceMultiplicativePrincipal.inputCheck_exact gamma current).mpr
      ⟨SourceLocalization.node_low gamma current hn, hfloor, hs.2.symm ▸ hm⟩
  have hmc' : SourceMultiplicativePrincipal.inputCheck (SourceOneIota.alphaCode root) current = true := by
    rw [ha.2]
    exact hmc
  have ho : SourceMultiplicativeTracking.rawWord gamma current ∈
      SourceAdditiveTracking.Assignment.execute (SourceOneIota.alphaCode root) current := by
    rw [ha.2]
    exact SourceAdditiveTracking.Assignment.execute_multiplicative gamma current hmc
  have hroot : Hereditary.interpretation 0 root = unionInterpretation gamma :=
    (MuPublicDictionary.Support.source_one_root gamma hg hl).2
  have hstrict : Hereditary.interpretation 0 root <
      interpretation (SourceOneIota.alphaCode root) current := by
    rw [ha.2, hroot, hs.2]
    exact hlt
  have he := SourceOneIota.GammaHat.FirstEntry.execute_lt_value_iff_firstCode_le_mu root current
    (SourceMultiplicativeTracking.rawWord gamma current) ha.1 hmc' ho hstrict
  have hf := PositiveHat.node_firstCode_value gamma current hn hmc
  have hmu := source_one_muValue gamma hg hl
  simpa only [ha.2, hs.2, hf, ← hmu, value, root, current] using he.symm

/-- Inside the original OWN interval, an actual source-one M-target
execution is a covering exactly below its genuine original semantic hat. -/
theorem execute_covering_iff_lt_value (gamma beta d : Nat) (out : List Nat)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (ho : out ∈ execute gamma beta)
    (hl : PublicEpsilonSourceDictionary.level gamma = 0)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    Covering gamma beta out ↔ unionInterpretation beta <
      value gamma ((inputCheck_exact gamma beta).mp (execute_spec gamma beta out ho).1).1 hl := by
  have hi := (execute_spec gamma beta out ho).1
  exact (CoveringConverse.execute_covering_iff_first gamma beta d out hd ho hlt).trans
    (search_first_iff_lt_value gamma beta d hi hd hl hm hlt)

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.SourceOneHat
