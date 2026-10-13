import Alexander313.Wilken.HereditaryNativeRelativeHighRewrite
import Alexander313.Wilken.HereditaryNativeRelativeHighRewriteGlobal
import Alexander313.Wilken.HereditaryNativeElementaryPublicReturn
import Alexander313.Wilken.HereditaryNativeLambdaSourceReturn

/-!
# Original bounded callers for the actual same-value public return

The original Delta has a genuine SAME-value alpha presentation with no
theta-zero calls: every original zero call is replaced by its public
parameter, and positive indices remain unchanged. The real exposed
comparison therefore bounds the argument of EVERY normal target zero
call below the original Delta whenever that call is below alpha-plus.
The complete principal-list bound supplies this endpoint condition to
every hidden zero call of an original LOW normal input. No extra hidden
caller, admission, comparison or translation oracle is assumed.
These are caller lemmas; the whole executing producer is separate.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedPublicReturn

open NativePublicBridge (contextCode contextCode_checked)
open Iota Iota.OrderInduction

/-- The original Convention 2.28 endpoint lies below the actual public
return endpoint. Coverage is used only to prove this numerical caller
bound; no chosen representative is used by the finite producer. -/
theorem sourceValue_lt_public_endpoint (s a : Nat) (ha : rootCheck s a = true) :
    AlphaPlus.sourceValue s a < finiteBase ((s + 1) + 1) := by
  obtain ⟨t, ht, hn, hl, hv⟩ := Lambda.SourceReturn.normal_low_representative s
    (AlphaPlus.sourceValue s a)
    (Lambda.SourceReturn.alphaPlus_lt_source_boundary s a (Bool.and_eq_true.mp ha).1)
  have hc : LowArithmetic.lowInput s t.code = true := by
    simp only [LowArithmetic.lowInput, lowCheckCode_code, lowCheck, ht, hl,
      decide_true, Bool.true_and]
  simpa only [interpretation_code, hv] using LowArithmetic.lowInput_bound s t.code hc

/-- The actual same-value source-to-alpha presentation contains no exposed
zero calls, even inside retained positive-index arguments. -/
theorem unshifted_exposed_zero (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (contextCode s) t = true)
    (hr : Restricted s a t) : exposedThetaList 0 (unshifted s a t) = [] := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; rfl
  | sum t u iht ihu =>
    intro ht hr
    have hc := BaseTransformation.sum_checks _ t u ht
    have hs := (restricted_sum s a t u).mp hr
    cases h : small s a (.sum t u) with
    | true => simp only [unshifted, h, Bool.cond_true, exposedThetaList]
    | false =>
      simp only [unshifted, h, Bool.cond_false, exposedThetaList,
        iht hc.1 hs.1, ihu hc.2 hs.2, List.nil_append]
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      rw [unshifted_below s a ha _ ht ((restricted_theta_zero s a t).mp hr).1]
      rfl
    | succ k =>
      rw [unshifted_theta_succ s a k ha t ht hr]
      simpa only [exposedThetaList, Nat.succ_ne_zero, if_false, Nat.succ_pos,
        if_true] using ih (BaseTransformation.theta_argument_check _ (k + 1) t ht)
          ((restricted_theta_succ s a k t).mp hr)

/-- The genuine original endpoint licenses a strictly smaller argument,
without a supplied high-head restriction or cross-context comparator. -/
theorem zero_argument_lt_delta (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) (.theta 0 t) = true)
    (hn : Comparison.Normal (alphaCode s a) t)
    (hb : denote (alphaCode s a) (.theta 0 t) < AlphaPlus.sourceValue s a) :
    denote (alphaCode s a) t < interpretation (contextCode s) (Lambda.deltaCode a) := by
  have hc := Lambda.argument_accepted s a ha
  have hd := (Decomposition.parts_checked (contextCode s) 0 (Lambda.argumentCode a) hc).1
  have hdn := (Decomposition.parts_normal (contextCode s) 0 (Lambda.argumentCode a) hc).1
  have hdr := Lambda.delta_restricted s a ha
  have he := Enclosure.delta_enclosure_spec s a ha
  have hbound : denote (alphaCode s a) (.theta 0 t) <
      denote (alphaCode s a) (.theta 0 (unshifted s a (Enclosure.deltaTerm a))) := by
    change denote (alphaCode s a) (.theta 0 t) <
      denote (alphaCode s a) (Enclosure.deltaEnclosureTerm s a)
    rw [AlphaPlus.delta_enclosure_eq_sourceValue s a ha]
    exact hb
  have hnil := unshifted_exposed_zero s a ha (Enclosure.deltaTerm a) hd hdr
  rcases (checked_theta_lt_iff_exposed (alphaCode s a) 0 t
    (unshifted s a (Enclosure.deltaTerm a)) ht he.1 hn
    (unshifted_normal s a ha _ hd hdn hdr)).mp hbound with h | h
  · have hv := unshifted_value s a ha (Enclosure.deltaTerm a) hd hdr
    simpa only [hv, Enclosure.deltaTerm, Lambda.deltaCode, Decomposition.highCode,
      interpretation_code] using h.1
  · obtain ⟨x, hx, hle⟩ := h
    rw [hnil] at hx
    exact False.elim (List.not_mem_nil hx)

/-- Every zero call of the original LOW normal input, including calls in
arbitrary hidden positive arguments, has the genuine endpoint bound. -/
theorem low_zero_calls_bounded (s a : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) t = true)
    (hn : Comparison.Normal (alphaCode s a) t) (hl : t.outerSort ≤ 1)
    (hb : denote (alphaCode s a) t < AlphaPlus.sourceValue s a) :
    ∀ u ∈ fullList t, denote (alphaCode s a) u < AlphaPlus.sourceValue s a := by
  intro u hu
  exact (Iota.Inverse.fullList_value_le_low _ t u ht hn hl hu).trans_lt hb

/-- The actual source decomposition of an inductively converted argument
has a high head below ORIGINAL Delta. This is a consequence of its genuine
same-value equation and the original target endpoint, not an extra guard. -/
theorem converted_highPart_lt_delta (s a c : Nat) (ha : rootCheck s a = true)
    (t : RelativeTerm Nat) (ht : check (alphaCode s a) (.theta 0 t) = true)
    (hn : Comparison.Normal (alphaCode s a) t)
    (hb : denote (alphaCode s a) (.theta 0 t) < AlphaPlus.sourceValue s a)
    (hc : Decomposition.inputCheck (contextCode s) c = true)
    (hv : interpretation (contextCode s) c = denote (alphaCode s a) t) :
    interpretation (contextCode s) (Decomposition.highCode 0 c) <
      interpretation (contextCode s) (Lambda.deltaCode a) := by
  have h := zero_argument_lt_delta s a ha t ht hn hb
  rw [← hv] at h
  exact (Decomposition.parts_le (contextCode s) 0 c hc).1.trans_lt h

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedPublicReturn
