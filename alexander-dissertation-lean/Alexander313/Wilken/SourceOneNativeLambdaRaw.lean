import Alexander313.Wilken.SourceOneNativeIotaEnclosure
import Alexander313.Wilken.SourceOneNativeMu

/-!
# Original raw source-one epsilon lambda, height and endpoint

The genuine original normalizer supplies the exact high-root lambda caller
on precisely original admitted epsilon theta-zero roots. Its output alpha
context has the ORIGINAL raw root value. Actual argument normalization
preserves the ORIGINAL alpha-plus endpoint. Output LOW, strict canonical
height descent and endpoint bounds follow from actual execution, with no
Normal, high-part, target-base, height or endpoint oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Lambda.Raw

abbrev normalizedRoot := Mu.Raw.normalizedRoot
abbrev inputCheck := Mu.Raw.inputCheck
abbrev outputContext := Mu.Raw.outputContext

theorem inputCheck_primrec : Primrec inputCheck := Mu.Raw.inputCheck_primrec

theorem inputCheck_exact (a : Nat) : inputCheck a = true ↔
    (∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧ check 0 (.theta 0 t) = true) ∧
      Ordinal.omega0 ^ interpretation 0 a = interpretation 0 a := Mu.Raw.inputCheck_exact a

theorem outputContext_value (a : Nat) (ha : inputCheck a = true) :
    NativeContext.base (outputContext a) = interpretation 0 a := Mu.Raw.outputContext_value a ha

def execute (a : Nat) : Part Nat := cond (inputCheck a) (Lambda.execute (normalizedRoot a)) Part.none

theorem execute_partrec : Partrec execute :=
  Partrec.cond inputCheck_primrec.to_comp
    (Lambda.execute_partrec.comp Mu.Raw.normalizedRoot_primrec.to_comp) Partrec.none

theorem execute_domain (a : Nat) : (execute a).Dom ↔ inputCheck a = true := by
  cases ha : inputCheck a with
  | false => simp only [execute, ha, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true =>
    simp only [execute, ha, Bool.cond_true, Lambda.execute_domain, (Bool.and_eq_true.mp ha).2]

theorem execute_graph (a out : Nat) : out ∈ execute a ↔
    inputCheck a = true ∧ out ∈ Lambda.execute (normalizedRoot a) := by
  cases h : inputCheck a <;> simp [execute, h]

theorem execute_spec (a out : Nat) (ho : out ∈ execute a) :
    inputCheck a = true ∧ NativeContext.lowCheckCode (outputContext a) out = true ∧
      NativeContext.Comparison.acceptedCode (outputContext a) out = true ∧
      NativeContext.interpretation (outputContext a) out =
        NativeContext.interpretation (outputContext a)
          (literalCode (normalizedRoot a) (Lambda.deltaCode (normalizedRoot a))) +
            SourceZeta.sourceValue 0 (normalizedRoot a) := by
  have hs := (execute_graph a out).mp ho
  have hl := Lambda.execute_spec _ out hs.2
  exact ⟨hs.1, Enclosure.lambda_low _ out hs.2, hl.2.1, hl.2.2⟩

theorem sourceAlphaPlus_normalized (a : Nat) (ha : inputCheck a = true) :
    Enclosure.sourceAlphaPlus (normalizedRoot a) = Enclosure.sourceAlphaPlus a := by
  have hv := SourceZeta.raw_argument_value 0 a (Bool.and_eq_true.mp ha).1
  change globalCollapse (finiteBase 0) 0
    (interpretation 0 (SourceZeta.argumentCode (Theta.Normalization.normalizeCode 0 a)) + 1) =
      globalCollapse (finiteBase 0) 0 (interpretation 0 (SourceZeta.argumentCode a) + 1)
  rw [hv]

theorem source_lemma_2_48_b (a out : Nat) (ho : out ∈ execute a) :
    NativeContext.interpretation (outputContext a) out < Enclosure.sourceAlphaPlus a := by
  have hs := (execute_graph a out).mp ho
  rw [← sourceAlphaPlus_normalized a hs.1]
  exact Enclosure.source_lemma_2_48_b _ out hs.2

private theorem source_checkCode (c : Nat) (hc : checkCode 0 c = true) :
    SourceOne.PublicCodes.checkCode c = true := by
  obtain ⟨t, rfl, ht⟩ := (checkCode_iff 0 c).mp hc
  simpa only [SourceOne.PublicCodes.checkCode_code, check_zero] using ht

theorem source_lemma_2_48_c (a out : Nat) (ho : out ∈ execute a) :
    NativeContext.CanonicalHeight.canonicalHeightCode (outputContext a) out <
      SourceOne.CanonicalHeight.canonicalHeightCode a := by
  have hs := (execute_graph a out).mp ho
  have hc : checkCode 0 a = true := (Bool.and_eq_true.mp (Bool.and_eq_true.mp hs.1).1).1
  have hn := Theta.Normalization.normalizeCode_checked 0 a hc
  have he := SourceOne.CanonicalHeight.canonicalHeightCode_invariant (normalizedRoot a) a
    (source_checkCode _ hn.1) (source_checkCode a hc)
    (by simpa only [interpretation_zero] using hn.2.2)
  rw [← he]
  exact Lambda.source_lemma_2_48_c _ out hs.2

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Lambda.Raw
