import Alexander313.Wilken.PublicEpsilonNativeReturnedIotaSupport

/-!
# Actual returned iota value with ORIGINAL source provenance

The finite producer retains original stopped parameters and zero-index
nodes. On the original checked Normal restricted domain it denotes exactly
the actual generic iota image. No arbitrary target payload return, source
representative, Normal transport, mapped value or endpoint invariance is
supplied. Literal executing guards and complete graphs retain zero.
Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ReturnedIota

open ThetaCourse

theorem root_scalar_caller (q b : Nat) (ha : PublicEpsilonIota.rootCheck q b = true) :
    RootLowCollapse.rootCheck q b = true :=
  (RootLowCollapse.rootCheck_exact q b).mpr ((PublicEpsilonIota.rootCheck_exact q b).mp ha).2.1

/-- Original full restriction derives every true theta-zero stop. The
executing scalar at a positive source index uses the genuine returned
recursive argument, without reconstructing a target canonical payload. -/
theorem returnedTreeCode_value (q b : Nat) (ha : PublicEpsilonIota.rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : PublicEpsilonIota.Restricted q b t) :
    interpretation q (returnedTreeCode q b t) =
      denote (PublicEpsilonIota.betaCode q b) (PublicEpsilonIota.transform q b t) := by
  revert ht hn hr
  induction t with
  | parameter p =>
    intro ht hn hr
    have hv := PublicEpsilonIota.OrderSupport.transform_low_value q b ha
      (.parameter p) ht hr (Nat.zero_le 1)
    simpa only [returnedTreeCode, interpretation_code] using hv.symm
  | sum t u iht ihu =>
    intro ht hn hr
    have hc := BaseTransformation.sum_checks q t u ht
    have hrs := (PublicEpsilonIota.restricted_sum q b t u).mp hr
    have hlt := returnedTreeCode_admitted q b (root_scalar_caller q b ha) t hc.1 hn.1
    have hrt := returnedTreeCode_admitted q b (root_scalar_caller q b ha) u hc.2 hn.2.1
    have hs := Arithmetic.addCode_spec q _ _
      ((Comparison.acceptedCode_exact q _).mp hlt.1).1
      ((Comparison.acceptedCode_exact q _).mp hrt.1).1
    change interpretation q (Arithmetic.addCode q _ _) = _
    rw [hs.2.1, iht hc.1 hn.1 hrs.1, ihu hc.2 hn.2.1 hrs.2]
    exact (PublicEpsilonIota.OrderSupport.transform_add q b ha t u hc.1 hc.2).symm
  | theta k t ih =>
    intro ht hn hr
    cases k with
    | zero =>
      have hb := ((PublicEpsilonIota.restricted_theta_zero q b t).mp hr).1
      have hv := (PublicEpsilonIota.transform_parameter_value q b ha (.theta 0 t) ht hb).2
      simpa only [returnedTreeCode, interpretation_code] using hv.symm
    | succ k =>
      have hc := FixedPoint.checked_theta_argument q (k + 1) t ht
      have hrs := (PublicEpsilonIota.restricted_theta_succ q b k t).mp hr
      have hs := returnedTreeCode_admitted q b (root_scalar_caller q b ha) t hc hn
      have hi := scalar_caller q b k (root_scalar_caller q b ha) t ht _ hs.1 hs.2
      have hv := (RootCompleteScalarCollapse.collapseCode_spec q b k _ hi).2
      rw [PublicEpsilonIota.OrderSupport.transform_theta_succ q b k ha t ht hr]
      change interpretation q (RootCompleteScalarCollapse.collapseCode q b k _) =
        globalCollapse (base (PublicEpsilonIota.betaCode q b)) k
          (denote (PublicEpsilonIota.betaCode q b) (PublicEpsilonIota.transform q b t))
      rw [hv, ih hc hn hrs, PublicEpsilonIota.beta_base q b ha]

theorem returnedTreeCode_low_value (q b : Nat) (ha : PublicEpsilonIota.rootCheck q b = true)
    (t : RelativeTerm Nat) (ht : check q t = true) (hn : Comparison.Normal q t)
    (hr : PublicEpsilonIota.Restricted q b t) (hl : t.outerSort ≤ 1) :
    interpretation q (returnedTreeCode q b t) = denote q t :=
  (returnedTreeCode_value q b ha t ht hn hr).trans
    (PublicEpsilonIota.OrderSupport.transform_low_value q b ha t ht hr hl)

def sourceTermCode (q b c : Nat) : Nat := (stateCode q b c).2.2

theorem sourceTermCode_primrec : Primrec₂ (fun ctx : Context => sourceTermCode ctx.1 ctx.2) :=
  (Primrec.snd.comp (Primrec.snd.comp stateCode_primrec)).to₂

theorem sourceTermCode_code (q b : Nat) (t : RelativeTerm Nat) :
    sourceTermCode q b t.code = returnedTreeCode q b t := by rw [sourceTermCode, stateCode_code]

/-- ALL original admitted Normal source trees have checked Normal
returned syntax, with no selected endpoint or restriction premise. -/
theorem sourceTermCode_admitted (q b c : Nat) (ha : RootLowCollapse.rootCheck q b = true)
    (hc : Comparison.acceptedCode q c = true) :
    Comparison.acceptedCode q (sourceTermCode q b c) = true ∧
      (rawTree (sourceTermCode q b c)).outerSort ≤ max 1 ((rawTree c).outerSort - 1) := by
  have hs := (Comparison.acceptedCode_exact q c).mp hc
  obtain ⟨t, he, ht⟩ := (checkCode_exact q c).mp hs.1
  have hn : Comparison.Normal q t := by simpa only [← he, rawTree_code] using hs.2
  simpa only [← he, sourceTermCode_code, rawTree_code] using returnedTreeCode_admitted q b ha t ht hn

abbrev inputCheck := PublicEpsilonIota.inputCheck

theorem inputCheck_primrec : Primrec₂ (fun ctx : Context => inputCheck ctx.1 ctx.2) :=
  PublicEpsilonIota.inputCheck_primrec

/-- The genuine original iota guard alone derives the returned-source
Normal code and its actual executing iota-image value. -/
theorem sourceTermCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    Comparison.acceptedCode q (sourceTermCode q b c) = true ∧
      interpretation q (sourceTermCode q b c) =
        interpretation (PublicEpsilonIota.betaCode q b) (PublicEpsilonIota.literalCode q b c) := by
  obtain ⟨ha, t, rfl, ht, hn, hr⟩ := (PublicEpsilonIota.inputCheck_exact q b c).mp hi
  have hrs := (PublicEpsilonIota.restricted_iff_sourceStar q b ha t ht hn).mpr hr
  rw [sourceTermCode_code, PublicEpsilonIota.literalCode_code q b ha t ht hn hrs, interpretation_code]
  exact ⟨(returnedTreeCode_admitted q b (root_scalar_caller q b ha) t ht hn).1,
    returnedTreeCode_value q b ha t ht hn hrs⟩

def literalCode (q b c : Nat) : Nat := cond (inputCheck q b c) (sourceTermCode q b c) 0

theorem literalCode_primrec : Primrec₂ (fun ctx : Context => literalCode ctx.1 ctx.2) :=
  (inputCheck_primrec.cond sourceTermCode_primrec (Primrec.const 0)).to₂

theorem literalCode_spec (q b c : Nat) (hi : inputCheck q b c = true) :
    Comparison.acceptedCode q (literalCode q b c) = true ∧
      interpretation q (literalCode q b c) =
        interpretation (PublicEpsilonIota.betaCode q b) (PublicEpsilonIota.literalCode q b c) := by
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
        interpretation (PublicEpsilonIota.betaCode q b) (PublicEpsilonIota.literalCode q b c) := by
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

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.ReturnedIota
