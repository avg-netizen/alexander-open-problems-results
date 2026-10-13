import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaOrderInduction
import Alexander313.Wilken.PublicEpsilonNativeReturnedIotaBaseChange

/-!
# Original-source provenance for the actual original-domain iota

The actual returned-source producer keeps original parameter syntax and
whole original theta-zero stops. Its existing admission and FULL original
Par/pi proofs use the genuine RootLow domain without a selected endpoint.
Here a direct syntax induction identifies that original producer with the
new whole-domain iota value. No old endpoint or iota-output Par is supplied.
The executing original-source output keeps the exact original admission,
Normality and full restriction guard; complete graphs include zero.
These proofs are uncompiled source candidates and a mu3.9 dependency.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.ReturnedSource

open ThetaCourse
open NativeContext.ReturnedIota
  (returnedTreeCode returnedTreeCode_admitted scalar_caller sourceTermCode
   sourceTermCode_primrec sourceTermCode_code sourceTermCode_admitted)

/-- Original full restriction derives every true theta-zero stop. The
executing scalar at a positive source index uses the genuine returned
recursive argument, without reconstructing a target canonical payload. -/
theorem returnedTreeCode_value (q b : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : PublicEpsilonUnboundedIota.Restricted q b t) :
    interpretation q (returnedTreeCode q b t) =
      denote (PublicEpsilonUnboundedIota.betaCode q b) (PublicEpsilonUnboundedIota.transform q b t) := by
  revert ht hn hr
  induction t with
  | parameter p =>
    intro ht hn hr
    have hv := PublicEpsilonUnboundedIota.OrderSupport.transform_low_value q b ha
      (.parameter p) ht hr (Nat.zero_le 1)
    simpa only [returnedTreeCode, interpretation_code] using hv.symm
  | sum t u iht ihu =>
    intro ht hn hr
    have hc := BaseTransformation.sum_checks q t u ht
    have hrs := (PublicEpsilonUnboundedIota.restricted_sum q b t u).mp hr
    have hlt := returnedTreeCode_admitted q b ha t hc.1 hn.1
    have hrt := returnedTreeCode_admitted q b ha u hc.2 hn.2.1
    have hs := Arithmetic.addCode_spec q _ _
      ((Comparison.acceptedCode_exact q _).mp hlt.1).1
      ((Comparison.acceptedCode_exact q _).mp hrt.1).1
    change interpretation q (Arithmetic.addCode q _ _) = _
    rw [hs.2.1, iht hc.1 hn.1 hrs.1, ihu hc.2 hn.2.1 hrs.2]
    exact (PublicEpsilonUnboundedIota.OrderSupport.transform_add q b ha t u hc.1 hc.2).symm
  | theta k t ih =>
    intro ht hn hr
    cases k with
    | zero =>
      have hb := ((PublicEpsilonUnboundedIota.restricted_theta_zero q b t).mp hr).1
      have hv := (PublicEpsilonUnboundedIota.transform_parameter_value q b ha (.theta 0 t) ht hb).2
      simpa only [returnedTreeCode, interpretation_code] using hv.symm
    | succ k =>
      have hc := FixedPoint.checked_theta_argument q (k + 1) t ht
      have hrs := (PublicEpsilonUnboundedIota.restricted_theta_succ q b k t).mp hr
      have hs := returnedTreeCode_admitted q b ha t hc hn
      have hi := scalar_caller q b k ha t ht _ hs.1 hs.2
      have hv := (RootCompleteScalarCollapse.collapseCode_spec q b k _ hi).2
      rw [PublicEpsilonUnboundedIota.OrderSupport.transform_theta_succ q b k ha t ht hr]
      change interpretation q (RootCompleteScalarCollapse.collapseCode q b k _) =
        globalCollapse (base (PublicEpsilonUnboundedIota.betaCode q b)) k
          (denote (PublicEpsilonUnboundedIota.betaCode q b) (PublicEpsilonUnboundedIota.transform q b t))
      rw [hv, ih hc hn hrs, PublicEpsilonUnboundedIota.beta_base q b ha]

theorem returnedTreeCode_low_value (q b : Nat) (ha : PublicEpsilonUnboundedIota.rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : PublicEpsilonUnboundedIota.Restricted q b t) (hl : t.outerSort ≤ 1) :
    interpretation q (returnedTreeCode q b t) = denote q t :=
  (returnedTreeCode_value q b ha t ht hn hr).trans
    (PublicEpsilonUnboundedIota.OrderSupport.transform_low_value q b ha t ht hr hl)

abbrev inputCheck := PublicEpsilonUnboundedIota.inputCheck

theorem inputCheck_primrec : Primrec₂ (fun ctx : Context => inputCheck ctx.1 ctx.2) :=
  PublicEpsilonUnboundedIota.inputCheck_primrec

/-- The genuine original iota guard alone derives the returned-source
Normal code and its actual executing iota-image value. -/
theorem sourceTermCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    Comparison.acceptedCode q (sourceTermCode q b c) = true ∧
      interpretation q (sourceTermCode q b c) =
        interpretation (PublicEpsilonUnboundedIota.betaCode q b) (PublicEpsilonUnboundedIota.literalCode q b c) := by
  obtain ⟨ha, t, rfl, ht, hn, hr⟩ := (PublicEpsilonUnboundedIota.inputCheck_exact q b c).mp hi
  have hrs := (PublicEpsilonUnboundedIota.restricted_iff_sourceStar q b ha t ht hn).mpr hr
  rw [sourceTermCode_code, PublicEpsilonUnboundedIota.literalCode_code q b ha t ht hn hrs, interpretation_code]
  exact ⟨(returnedTreeCode_admitted q b ha t ht hn).1,
    returnedTreeCode_value q b ha t ht hn hrs⟩

def literalCode (q b c : Nat) : Nat := cond (inputCheck q b c) (sourceTermCode q b c) 0

theorem literalCode_primrec : Primrec₂ (fun ctx : Context => literalCode ctx.1 ctx.2) :=
  (inputCheck_primrec.cond sourceTermCode_primrec (Primrec.const 0)).to₂

theorem literalCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    Comparison.acceptedCode q (literalCode q b c) = true ∧
      interpretation q (literalCode q b c) =
        interpretation (PublicEpsilonUnboundedIota.betaCode q b) (PublicEpsilonUnboundedIota.literalCode q b c) := by
  simpa only [literalCode, hi, Bool.cond_true] using sourceTermCode_spec q b c hi

theorem literalCode_rejected (q b c : Nat) (hi : inputCheck q b c = false) : literalCode q b c = 0 := by
  simp only [literalCode, hi, Bool.cond_false]

def execute (q b c : Nat) : Part Nat := cond (inputCheck q b c) (Part.some (literalCode q b c)) Part.none

theorem execute_partrec : Partrec₂ (fun ctx : Context => execute ctx.1 ctx.2) :=
  (Partrec.cond inputCheck_primrec.to_comp literalCode_primrec.to_comp.partrec Partrec.none).to₂

theorem execute_dom (q b c : Nat) : (execute q b c).Dom ↔ inputCheck q b c = true := by
  cases hi : inputCheck q b c <;> simp [execute, hi]

theorem execute_graph (q b c out : Nat) : out ∈ execute q b c ↔
    inputCheck q b c = true ∧ out = literalCode q b c := by
  cases hi : inputCheck q b c <;> simp [execute, hi]

theorem execute_spec (q b c out : Nat) (ho : out ∈ execute q b c) :
    Comparison.acceptedCode q out = true ∧
      interpretation q out =
        interpretation (PublicEpsilonUnboundedIota.betaCode q b) (PublicEpsilonUnboundedIota.literalCode q b c) := by
  obtain ⟨hi, rfl⟩ := (execute_graph q b c out).mp ho
  exact literalCode_spec q b c hi

def graphBool (q b c out : Nat) : Bool := inputCheck q b c && (out == literalCode q b c)

theorem graphBool_primrec : Primrec
    (fun p : (Context × Nat) × Nat => graphBool p.1.1.1 p.1.1.2 p.1.2 p.2) :=
  Primrec.and.comp (inputCheck_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (literalCode_primrec.comp Primrec.fst))

theorem graphBool_exact (q b c out : Nat) : graphBool q b c out = true ↔ out ∈ execute q b c := by
  rw [execute_graph]
  simp only [graphBool, Bool.and_eq_true, beq_iff_eq]

/-- The actual original-source returned code has FULL original Par and a
real pi caller derived from chosen root and input Par. Target iota parameter
payloads are never assumed to lie below the smaller original source base. -/
theorem sourceTermCode_full_par_pi (q v b c : Nat) (hi : inputCheck q b c = true)
    (hv : baseCheck v = true) (hl : base v < base q)
    (hpb : BaseTransformation.ParBounded q v (rawTree b))
    (hpc : BaseTransformation.ParBounded q v (rawTree c)) :
    BaseTransformation.ParBounded q v (rawTree (sourceTermCode q b c)) ∧
      BaseTransformation.inputCheck q v (sourceTermCode q b c) = true ∧
      BaseTransformation.piCode q v (sourceTermCode q b c) =
        sourceTermCode v (BaseTransformation.piCode q v b) (BaseTransformation.piCode q v c) := by
  obtain ⟨ha, t, he, ht, hn, hs⟩ := (PublicEpsilonUnboundedIota.inputCheck_exact q b c).mp hi
  have hc : Comparison.acceptedCode q c = true :=
    (Bool.and_eq_true.mp (Bool.and_eq_true.mp hi).2).1
  exact ⟨NativeContext.ReturnedIota.sourceTermCode_parBounded q v b c ha hc hv hpb hpc,
    NativeContext.ReturnedIota.sourceTermCode_pi_caller q v b c ha hc hv hl hpb hpc,
    NativeContext.ReturnedIota.piCode_sourceTermCode q v b c ha hc hv hl hpb hpc⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.ReturnedSource
