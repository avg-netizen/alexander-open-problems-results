import Alexander313.Wilken.HereditaryNativeRelativeHighRewriteGlobal
import Alexander313.Wilken.HereditaryNativeElementaryPublicReturn
import Alexander313.Wilken.SourceOneNativeMuBounds

/-!
# Genuine bounded callers for source-one SAME-value return

The ORIGINAL source-zero checker and theta dictionary are retained.
The original Delta has a SAME-value alpha presentation with no exposed
zero calls. Actual exposed comparison bounds every target zero argument
below ORIGINAL Delta; the complete LOW principal bound supplies that
caller to all hidden high arguments. No support or translator oracle.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedPublicReturn

open OrderSupport HeightSupport
open NativeContext.Iota.OrderInduction (checked_theta_lt_iff_exposed)

theorem sourceAlphaPlus_lt_public_endpoint (a : Nat) (ha : rootCheck a = true) :
    Enclosure.sourceAlphaPlus a < finiteBase 1 := by
  simpa only [finiteBase_succ] using Mu.Bounds.source_alphaPlus_lt_source_boundary a ha

theorem unshifted_exposed_zero (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : check 0 t = true) (hr : Restricted a t) :
    exposedThetaList 0 (unshifted a t) = [] := by
  revert ht hr
  induction t with
  | parameter p => intro ht hr; rfl
  | sum t u iht ihu =>
    intro ht hr
    have hc := sum_checks t u ht
    have hs := (restricted_sum a t u).mp hr
    cases h : small a (.sum t u) with
    | true => simp only [unshifted, h, Bool.cond_true, exposedThetaList]
    | false =>
      simp only [unshifted, h, Bool.cond_false, exposedThetaList,
        iht hc.1 hs.1, ihu hc.2 hs.2, List.nil_append]
  | theta k t ih =>
    intro ht hr
    cases k with
    | zero =>
      rw [unshifted_below a ha _ ht ((restricted_theta_zero a t).mp hr).1]
      rfl
    | succ k =>
      rw [unshifted_theta_succ a k ha t ht hr]
      simpa only [exposedThetaList, Nat.succ_ne_zero, if_false, Nat.succ_pos,
        if_true] using ih (argument_checked (k + 1) t ht)
          ((restricted_theta_succ a k t).mp hr)

theorem zero_argument_lt_delta (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) (.theta 0 t) = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t)
    (hb : NativeContext.denote (alphaCode a) (.theta 0 t) < Enclosure.sourceAlphaPlus a) :
    NativeContext.denote (alphaCode a) t < interpretation 0 (Lambda.deltaCode a) := by
  have hc := Lambda.argument_accepted a ha
  have hd := (SourceDecomposition.parts_checked 0 0 (Lambda.argumentCode a) hc).1
  have hdn := (SourceDecomposition.parts_normal 0 0 (Lambda.argumentCode a) hc).1
  have hdr := Lambda.delta_restricted a ha
  have he := Enclosure.delta_enclosure_spec a ha
  have hbound : NativeContext.denote (alphaCode a) (.theta 0 t) <
      NativeContext.denote (alphaCode a) (.theta 0 (unshifted a (Enclosure.deltaTerm a))) := by
    change NativeContext.denote (alphaCode a) (.theta 0 t) <
      NativeContext.denote (alphaCode a) (Enclosure.deltaEnclosureTerm a)
    rw [Enclosure.delta_enclosure_eq_sourceAlphaPlus a ha]
    exact hb
  have hnil := unshifted_exposed_zero a ha (Enclosure.deltaTerm a) hd hdr
  rcases (checked_theta_lt_iff_exposed (alphaCode a) 0 t
    (unshifted a (Enclosure.deltaTerm a)) ht he.1 hn
    (unshifted_normal a ha _ hd hdn hdr)).mp hbound with h | h
  · have hv := unshifted_value a ha (Enclosure.deltaTerm a) hd hdr
    simpa only [hv, Enclosure.deltaTerm, Lambda.deltaCode, OmegaQuotient.deltaCode,
      SourceDecomposition.highCode, interpretation_code] using h.1
  · obtain ⟨x, hx, hle⟩ := h
    rw [hnil] at hx
    exact False.elim (List.not_mem_nil hx)

theorem low_zero_calls_bounded (a : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) t = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t) (hl : t.outerSort ≤ 1)
    (hb : NativeContext.denote (alphaCode a) t < Enclosure.sourceAlphaPlus a) :
    ∀ u ∈ fullList t, NativeContext.denote (alphaCode a) u < Enclosure.sourceAlphaPlus a := by
  intro u hu
  exact (NativeContext.Iota.Inverse.fullList_value_le_low _ t u ht hn hl hu).trans_lt hb

theorem converted_highPart_lt_delta (a c : Nat) (ha : rootCheck a = true)
    (t : RelativeTerm Nat) (ht : NativeContext.check (alphaCode a) (.theta 0 t) = true)
    (hn : NativeContext.Comparison.Normal (alphaCode a) t)
    (hb : NativeContext.denote (alphaCode a) (.theta 0 t) < Enclosure.sourceAlphaPlus a)
    (hc : SourceDecomposition.inputCheck 0 c = true)
    (hv : interpretation 0 c = NativeContext.denote (alphaCode a) t) :
    interpretation 0 (SourceDecomposition.highCode 0 0 c) <
      interpretation 0 (Lambda.deltaCode a) := by
  have h := zero_argument_lt_delta a ha t ht hn hb
  rw [← hv] at h
  exact (SourceDecomposition.parts_le 0 0 c hc).1.trans_lt h

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedPublicReturn
