import Alexander313.Wilken.PublicEpsilonNativeMultiplicativePrincipal
import Alexander313.Wilken.HereditaryNativeLogEnd
import Alexander313.Wilken.HereditaryNativeBaseLeftMultiplication
import Alexander313.Wilken.MultiplicativeFactorRemoval

/-!
# Actual native factors for the additive-principal assignment

The real native last logarithm supplies a Normal LOW exponent. Its original
ANF is mapped through the genuine same-context omega-power producer. The
retained exponent prefix is built from precisely the original retained
atoms, and the final exponent atom comes from the actual native parser.
These are finite native producers with derived admission and values.
No supplied factorization, prefix, last factor or endpoint is used.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FactorSupport

open ThetaCourse
open Hereditary.FinePredecessor (stripLast stripLast_primrec stripLast_mem stripLast_split)
open MultiplicativeNormalForm MultiplicativePrincipalArithmetic

/-- Two genuine native powers construct the literal source cutoff tau^omega. -/
def cutoffCode (q : Nat) : Nat := OmegaPowers.powerCode q
  (OmegaPowers.powerCode q (Arithmetic.addCode q OmegaPowers.Offsets.baseCode
    (OmegaPowerHeight.numeralCode 1)))

theorem cutoffCode_primrec : Primrec cutoffCode := by
  have ha := Arithmetic.addCode_primrec.comp
    (Primrec.id.pair ((Primrec.const OmegaPowers.Offsets.baseCode).pair
      (Primrec.const (OmegaPowerHeight.numeralCode 1))))
  have hp := OmegaPowers.powerCode_primrec.comp Primrec.id ha
  exact OmegaPowers.powerCode_primrec.comp Primrec.id hp

theorem cutoffCode_spec (q : Nat) (hq : baseCheck q = true) :
    lowCheckCode q (cutoffCode q) = true ∧ Comparison.acceptedCode q (cutoffCode q) = true ∧
      interpretation q (cutoffCode q) = base q ^ Ordinal.omega0 := by
  have hb := OmegaPowers.Offsets.baseCode_spec q hq
  have hn := OmegaPowerHeight.numeralCode_spec q 1 hq
  have hs := Arithmetic.addCode_spec q OmegaPowers.Offsets.baseCode
    (OmegaPowerHeight.numeralCode 1) ((Comparison.acceptedCode_exact q _).mp hb.1).1
      ((Comparison.acceptedCode_exact q _).mp hn.2.1).1
  have hlo := (OmegaPowerHeight.addCode_low_height q _ _
    (BaseLeftMultiplication.baseCode_low q hq) hn.1).1
  have hp := OmegaPowers.powerCode_spec q _ hlo
  have ht := OmegaPowers.powerCode_spec q _ hp.1
  refine ⟨ht.1, ht.2.1, ?_⟩
  change interpretation q (OmegaPowers.powerCode q _) = _
  rw [ht.2.2, hp.2.2, hs.2.1, hb.2, hn.2.2.1, Nat.cast_one,
    Ordinal.opow_add_one, SourceChi.epsilon_base q hq, Ordinal.opow_mul,
    SourceChi.epsilon_base q hq]

def prefixTerm (d : Nat) : RelativeTerm Nat :=
  Normalization.buildAtoms (stripLast (Decomposition.word d))

def prefixExponentCode (d : Nat) : Nat := (prefixTerm d).code

theorem prefixTerm_primrec : Primrec prefixTerm :=
  Normalization.Effective.buildAtoms_primrec.comp (stripLast_primrec.comp Decomposition.word_primrec)

theorem prefixExponentCode_primrec : Primrec prefixExponentCode := code_primrec.comp prefixTerm_primrec

theorem prefixExponentCode_spec (q d : Nat) (hd : lowCheckCode q d = true)
    (hn : Comparison.acceptedCode q d = true) :
    lowCheckCode q (prefixExponentCode d) = true ∧
      Comparison.acceptedCode q (prefixExponentCode d) = true ∧
      interpretation q (prefixExponentCode d) =
        principalSum ((stripLast (Decomposition.word d)).map (denote q)) := by
  let n := SourceOne.PublicCodes.fragment (rawTree d)
  have hq := (HeightBoundary.input_spec q d hd).2.1
  have hw := Decomposition.word_good q n d hn (SourceOne.PublicCodes.height_le_fragment _)
  have hs : (stripLast (Decomposition.word d)).Sublist (Decomposition.word d) := by
    simpa only [stripLast, List.reverse_reverse] using
      (List.tail_sublist (Decomposition.word d).reverse).reverse
  have hg : Normalization.GoodAtoms q n (stripLast (Decomposition.word d)) :=
    fun a ha => hw a (hs.subset ha)
  have ha := Normalization.buildAtoms_admissible q n hq _ hg
  have had : IsAdditiveNormalForm ((stripLast (Decomposition.word d)).map (denote q)) := by
    have hu := hs.map (denote q)
    have hnormal := Decomposition.word_normal q d hn
    exact ⟨fun a ham => hnormal.1 a (hu.subset ham), hnormal.2.sublist hu⟩
  have hnormal := Normalization.buildAtoms_normal q n _ hg had
  have haccept : Comparison.acceptedCode q (prefixExponentCode d) = true := by
    apply (Comparison.acceptedCode_exact q _).mpr
    refine ⟨?_, ?_⟩
    · simpa only [prefixExponentCode, prefixTerm, checkCode_code] using
        Comparison.admitted_checked q n hq _ ha
    · simpa only [prefixExponentCode, prefixTerm, rawTree_code] using hnormal
  have hv : interpretation q (prefixExponentCode d) =
      principalSum ((stripLast (Decomposition.word d)).map (denote q)) := by
    simp only [prefixExponentCode, interpretation_code, prefixTerm, Normalization.buildAtoms_denote]
  have hb : interpretation q (prefixExponentCode d) < omegaSequence (base q) 1 := by
    rw [hv]
    apply principalSum_lt (omegaSequence_isSuccLimit (base q) 0).bot_lt
      (omegaSequence_add_closed (base q) 0) _
    intro a ham
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ham
    have hm : denote q t ∈ canonicalANF (interpretation q d) := by
      rw [← (Decomposition.word_spec q d hn).2]
      exact List.mem_map.mpr ⟨t, hs.subset ht, rfl⟩
    exact (canonicalANF_mem_le hm).trans_lt ((HeightBoundary.input_spec q d hd).2.2)
  exact ⟨OmegaPowers.low_of_bound q _ ((Comparison.acceptedCode_exact q _).mp haccept).1 hb,
    haccept, hv⟩

def factorWord (q d : Nat) : List Nat :=
  (Decomposition.word d).map fun t => OmegaPowers.powerCode q t.code

theorem factorWord_primrec : Primrec₂ factorWord := by
  have ht : Primrec₂ (fun p : Nat × Nat => fun t : RelativeTerm Nat =>
      OmegaPowers.powerCode p.1 t.code) :=
    (OmegaPowers.powerCode_primrec.comp (Primrec.fst.comp Primrec.fst)
      (code_primrec.comp Primrec.snd)).to₂
  exact (Primrec.list_map (Decomposition.word_primrec.comp Primrec.snd) ht).to₂

theorem factorWord_spec (q d : Nat) (hd : lowCheckCode q d = true)
    (hn : Comparison.acceptedCode q d = true) :
    (∀ c ∈ factorWord q d, lowCheckCode q c = true ∧ Comparison.acceptedCode q c = true) ∧
      (factorWord q d).map (interpretation q) = omegaFactors (interpretation q d) := by
  have hatom (t : RelativeTerm Nat) (ht : t ∈ Decomposition.word d) : lowCheckCode q t.code = true := by
    apply OmegaPowers.low_of_bound q _
      (by simpa only [checkCode_code] using ((Decomposition.word_spec q d hn).1 t ht).1)
    have hm : denote q t ∈ canonicalANF (interpretation q d) := by
      rw [← (Decomposition.word_spec q d hn).2]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩
    simpa only [interpretation_code] using
      (canonicalANF_mem_le hm).trans_lt ((HeightBoundary.input_spec q d hd).2.2)
  constructor
  · intro c hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    have hp := OmegaPowers.powerCode_spec q t.code (hatom t ht)
    exact ⟨hp.1, hp.2.1⟩
  · change ((Decomposition.word d).map _).map _ = _
    rw [List.map_map]
    calc
      (Decomposition.word d).map (fun t => interpretation q (OmegaPowers.powerCode q t.code)) =
          (Decomposition.word d).map (fun t => Ordinal.omega0 ^ denote q t) := by
        apply List.map_congr_left
        intro t ht
        simpa only [interpretation_code] using
          (OmegaPowers.powerCode_spec q t.code (hatom t ht)).2.2
      _ = omegaFactors (interpretation q d) := by
        rw [omegaFactors, ← (Decomposition.word_spec q d hn).2, List.map_map]

def prefixCode (q d : Nat) : Nat := OmegaPowers.powerCode q (prefixExponentCode d)

def lastCode (q d : Nat) : Nat := OmegaPowers.powerCode q (LogEndZero.endCode d)

theorem prefixCode_primrec : Primrec₂ prefixCode :=
  OmegaPowers.powerCode_primrec.comp Primrec.fst (prefixExponentCode_primrec.comp Primrec.snd)

theorem lastCode_primrec : Primrec₂ lastCode :=
  OmegaPowers.powerCode_primrec.comp Primrec.fst (LogEndZero.endCode_primrec.comp Primrec.snd)

theorem prefixCode_spec (q d : Nat) (hd : lowCheckCode q d = true)
    (hn : Comparison.acceptedCode q d = true) :
    lowCheckCode q (prefixCode q d) = true ∧ Comparison.acceptedCode q (prefixCode q d) = true ∧
      interpretation q (prefixCode q d) = factorProduct (factorPrefix (omegaFactors (interpretation q d))) := by
  have hs := prefixExponentCode_spec q d hd hn
  have hp := OmegaPowers.powerCode_spec q _ hs.1
  refine ⟨hp.1, hp.2.1, ?_⟩
  rw [prefixCode, hp.2.2, hs.2.2, omegaFactors, ← (Decomposition.word_spec q d hn).2]
  simp only [factorPrefix, stripLast, List.map_reverse, List.map_tail]
  exact (factorProduct_omega_map _).symm

theorem lastCode_spec (q d : Nat) (hd : lowCheckCode q d = true)
    (hn : Comparison.acceptedCode q d = true) (hz : interpretation q d ≠ 0) :
    lowCheckCode q (lastCode q d) = true ∧ Comparison.acceptedCode q (lastCode q d) = true ∧
      interpretation q (lastCode q d) = lastFactor (omegaFactors (interpretation q d)) := by
  have hs := LogEnd.Support.endCode_spec q d hd hn hz
  have hp := OmegaPowers.powerCode_spec q _ hs.1
  refine ⟨hp.1, hp.2.1, ?_⟩
  rw [lastCode, hp.2.2, LogEndZero.endCode_value q d hn, lastFactor_omegaFactors]
  rfl

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.FactorSupport
