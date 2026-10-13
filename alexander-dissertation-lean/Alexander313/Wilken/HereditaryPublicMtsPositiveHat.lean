import Alexander313.Wilken.HereditaryPublicMtsCoveringConverse
import Alexander313.Wilken.PublicEpsilonNativeGammaHatFirstEntry

/-!
# Actual selected positive-source covering and the semantic singleton cut

The selected positive original source supplies the genuine root and its
literal canonical beta code. Its actual public mu is the original mu.
Real native multiplicative execution agrees with the independent Node
word in VALUES, so its FIRST is the FIRST used by the least-cover test.
The proved original singleton-minimum criterion therefore identifies the
actual emitted covering with the semantic hat cut inside the true OWN
interval. This does not execute the minimum or claim the source-one hat
case, outside-cut reach, full mts domain or large h. Uncompiled candidates.
-/

noncomputable section

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.PositiveHat

open NativeContext
open NativeContext.PublicEpsilonUnboundedIota
open FirstSupport
open CoveringSupport (Covering)

/-- The genuine selected original positive-source root defines the
already proved semantic least singleton boundary, with its actual guard. -/
def value (gamma : Nat) (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma ≠ 0) : Ordinal.{0} :=
  GammaHat.value (MuPublicDictionary.Support.nativeContext gamma)
    (MuPublicDictionary.Support.nativeRoot gamma) (ContextSupport.positive_base gamma hg hl).1

theorem positive_muValue (gamma : Nat)
    (hg : MuPublicDictionary.Support.inputCheck gamma = true)
    (hl : PublicEpsilonSourceDictionary.level gamma ≠ 0) :
    SkPublicRecurrence.muValue gamma = Mu.sourceValue
      (MuPublicDictionary.Support.nativeContext gamma) (MuPublicDictionary.Support.nativeRoot gamma) := by
  have hz := beq_eq_false_iff_ne.mpr hl
  simpa only [SkPublicRecurrence.muValue, (MuPublicDictionary.publicCode_spec gamma hg).2,
    MuPublicDictionary.Support.sourceValue, hz, Bool.cond_false]

/-- Actual raw multiplicative execution and the actual Node word have
the same FIRST in VALUES, without any literal native spelling injection. -/
theorem node_firstCode_value (gamma current : Nat)
    (hn : SourceLocalization.Node gamma current)
    (hm : SourceMultiplicativePrincipal.inputCheck gamma current = true) :
    interpretation gamma (SourceAdditiveTracking.Insertion.firstCode
      (SourceMultiplicativeTracking.rawWord gamma current)) = firstValue gamma current := by
  have hi := (SourceLocalization.inputCheck_exact gamma current).mpr hn
  have hv := SourceMultiplicativeTracking.RawRecurrence.rawWord_values_word gamma current hi
  obtain ⟨first, tail, hw, hfirst⟩ := word_first_shape gamma current
  have hraw := SourceAdditiveTracking.Assignment.execute_multiplicative gamma current hm
  have hne := SourceAdditiveTracking.Assignment.execute_nonempty gamma current _ hraw
  obtain ⟨a, rest, ha⟩ := List.exists_cons_of_ne_nil hne
  have he : interpretation gamma a = interpretation gamma first :=
    (List.cons.inj (by simpa only [ha, hw, List.map_cons] using hv)).1
  simpa only [ha, SourceAdditiveTracking.Insertion.firstCode, List.head?_cons,
    Option.getD_some] using he.trans hfirst.symm

/-- The true original positive source and actual native M caller turn the
semantic singleton-boundary criterion into the independent public FIRST cut. -/
theorem search_first_iff_lt_value (gamma beta d : Nat)
    (hi : inputCheck gamma beta = true) (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (hl : PublicEpsilonSourceDictionary.level gamma ≠ 0)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    firstValue gamma (nativeRoot gamma d) ≤ SkPublicRecurrence.muValue gamma ↔
      unionInterpretation beta < value gamma ((inputCheck_exact gamma beta).mp hi).1 hl := by
  have hg := ((inputCheck_exact gamma beta).mp hi).1
  have ha := ContextSupport.positive_base gamma hg hl
  let q := MuPublicDictionary.Support.nativeContext gamma
  let root := MuPublicDictionary.Support.nativeRoot gamma
  let current := nativeRoot gamma d
  have hs := nativeRoot_spec gamma beta d hi hd
  have hn := (SourceLocalization.inputCheck_exact gamma current).mp hs.1
  have hfloor : base gamma ≤ interpretation gamma current := by
    rw [hs.2]
    exact ((inputCheck_exact gamma beta).mp hi).2.2.2.2.1
  have hmc : SourceMultiplicativePrincipal.inputCheck gamma current = true :=
    (SourceMultiplicativePrincipal.inputCheck_exact gamma current).mpr
      ⟨SourceLocalization.node_low gamma current hn, hfloor, hs.2.symm ▸ hm⟩
  have hmc' : SourceMultiplicativePrincipal.inputCheck (betaCode q root) current = true := by
    rw [ha.2]
    exact hmc
  have ho : SourceMultiplicativeTracking.rawWord gamma current ∈
      SourceAdditiveTracking.Assignment.execute (betaCode q root) current := by
    rw [ha.2]
    exact SourceAdditiveTracking.Assignment.execute_multiplicative gamma current hmc
  have hroot : interpretation q root = unionInterpretation gamma :=
    (MuPublicDictionary.Support.native_root gamma hg hl).2
  have hstrict : interpretation q root < interpretation (betaCode q root) current := by
    rw [ha.2, hroot, hs.2]
    exact hlt
  have he := GammaHat.FirstEntry.execute_lt_value_iff_firstCode_le_mu q root current
    (SourceMultiplicativeTracking.rawWord gamma current) ha.1 hmc' ho hstrict
  have hf := node_firstCode_value gamma current hn hmc
  have hmu := positive_muValue gamma hg hl
  simpa only [ha.2, hs.2, hf, ← hmu, value, q, root, current] using he.symm

/-- Within the actual OWN domain, a genuine M target has an emitted
covering exactly below the genuine selected positive-source semantic hat. -/
theorem execute_covering_iff_lt_value (gamma beta d : Nat) (out : List Nat)
    (hd : d ∈ SkNextSearch.Support.search gamma beta)
    (ho : out ∈ execute gamma beta)
    (hl : PublicEpsilonSourceDictionary.level gamma ≠ 0)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation beta))
    (hlt : unionInterpretation gamma < unionInterpretation beta) :
    Covering gamma beta out ↔ unionInterpretation beta <
      value gamma ((inputCheck_exact gamma beta).mp (execute_spec gamma beta out ho).1).1 hl := by
  have hi := (execute_spec gamma beta out ho).1
  exact (CoveringConverse.execute_covering_iff_first gamma beta d out hd ho hlt).trans
    (search_first_iff_lt_value gamma beta d hi hd hl hm hlt)

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.PositiveHat
