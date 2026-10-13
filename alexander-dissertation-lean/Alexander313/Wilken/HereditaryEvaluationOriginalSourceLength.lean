import Alexander313.Wilken.HereditaryEvaluationInitialHeightPublicAgreement
import Alexander313.Wilken.HereditaryEvaluationComponentReferenceLength
import Alexander313.Wilken.HereditarySourceOneRelativeAssignment

/-!
# Actual component length bounded by its original LOW input height

The genuine RAW parser reconstructs a checked original HIGH root of a
proper FIRST epsilon. Its public initial height equals the original LOW
canonical height, by actual equal-value height invariance. The independent
public tracking certificate bounds the whole word at FIRST; original LOW
height monotonicity and actual assignment ALL bounds compare FIRST with
the original input. Both original zero and the genuine finite positive
source are included. This does not invent a LOW representative at the
grammar upper boundary or prove recursive evaluation descent. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationOriginalSourceLength

open EvaluationInitialReferenceHeight
open NativeContext.SourceAdditiveTracking.Insertion (firstCode)
open Hereditary.FinePredecessor (stripLast)
open NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support (stripLast_cons_nonempty)

theorem source_one_raw_height (c : Nat)
    (hc : SourceOneIota.SourceTrackingRaw.Support.inputCheck c = true) :
    initialHeight (SourceOneIota.SourceTrackingRaw.Support.publicCode c) =
      SourceOne.CanonicalHeight.canonicalHeightCode c := by
  have hr := SourceOneIota.SourceTrackingRaw.Support.rootCode_spec c hc
  let root := SourceOneIota.SourceTrackingRaw.Support.rootCode c
  have hp := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec c hr.1
  have hl := SourceOneIota.root_low root hr.2.1
  have hroot := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec root hl
  have he : SourceOneIota.SourceTrackingRaw.Support.publicCode c =
      SourceOneIota.SourceTrackingRaw.Support.publicCode root :=
    Canonical.check_value_injective _ _ hp.1 hroot.1 (hp.2.trans (hr.2.2.symm.trans hroot.2.symm))
  have hlow : SourceOne.PublicCodes.lowCheckCode c = true := by
    simpa only [lowCheckCode_zero] using hr.1
  have hv : SourceOne.PublicCodes.interpretation root = SourceOne.PublicCodes.interpretation c := by
    simpa only [interpretation_zero] using hr.2.2
  have hh := SourceOne.CanonicalHeight.canonicalHeightCode_invariant root c
    (Bool.and_eq_true.mp (SourceOneIota.HeightSupport.root_source_accepted root hr.2.1)).1
    (SourceOne.HeightBoundary.input_spec c hlow).1 hv
  rw [he, EvaluationInitialHeightPublicAgreement.source_one root hr.2.1, hh]

theorem positive_raw_height (s c : Nat)
    (hc : NativeContext.SourceTrackingRaw.Support.inputCheck (NativePublicBridge.contextCode s) c = true) :
    initialHeight (NativeContext.UniformPublicReturn.publicCode (NativePublicBridge.contextCode s) c) =
      NativeContext.CanonicalHeight.canonicalHeightCode (NativePublicBridge.contextCode s) c := by
  let q := NativePublicBridge.contextCode s
  let root := NativeContext.SourceTrackingRaw.Support.rootCode q c
  have hr := NativeContext.SourceTrackingRaw.Support.rootCode_spec q c hc
  have hp := NativeContext.UniformPublicReturn.publicCode_spec q c
    ((NativeContext.UniformPublicReturn.inputCheck_exact q c).mpr hr.1)
  have hroot := NativeContext.UniformPublicReturn.publicCode_spec q root
    ((NativeContext.UniformPublicReturn.inputCheck_exact q root).mpr
      (NativeContext.RootLowCollapse.root_low q root hr.2.1))
  have he : NativeContext.UniformPublicReturn.publicCode q c =
      NativeContext.UniformPublicReturn.publicCode q root :=
    Canonical.check_value_injective _ _ hp.1 hroot.1 (hp.2.trans (hr.2.2.symm.trans hroot.2.symm))
  have hh := NativeContext.CanonicalHeight.canonicalHeightCode_invariant q root c
    (NativeContext.RootLowCollapse.root_original q root hr.2.1)
    (Bool.and_eq_true.mp hr.1).1 hr.2.2
  rw [he, EvaluationInitialHeightPublicAgreement.positive s root hr.2.1, hh]

theorem source_one_assignment_length (input : Nat) (word : List Nat)
    (ho : word ∈ SourceOneIota.SourceAdditiveTracking.Assignment.execute input) :
    word.length ≤ SourceOne.CanonicalHeight.canonicalHeightCode input + 1 := by
  have ht := SourceOneIota.SourceAdditiveTracking.Assignment.execute_tracking input word ho
  have hp := GlobalAdditiveTracking.RelativeCertificate.source_one_tracking word ht
  have hi := (SourceOneIota.SourceAdditiveTracking.Assignment.inputCheck_exact input).mp
    (SourceOneIota.SourceAdditiveTracking.Assignment.execute_spec input word ho).1
  cases word with
  | nil => exact False.elim (SourceOneIota.SourceAdditiveTracking.Assignment.execute_nonempty input [] ho rfl)
  | cons first rest =>
    cases rest with
    | nil => simp only [List.length_singleton]; omega
    | cons next rest =>
      have hr := (SourceOneIota.SourceTrackingRaw.trackingCheck_exact _).mp ht
      have hf : SourceOneIota.SourceTrackingRaw.Support.inputCheck first = true := by
        apply hr.2.1.nodes first
        rw [stripLast_cons_nonempty first (next :: rest) (List.cons_ne_nil _ _)]
        exact List.mem_cons_self
      have hflow : SourceOne.PublicCodes.lowCheckCode first = true := by
        simpa only [lowCheckCode_zero] using (SourceOneIota.SourceTrackingRaw.Support.rootCode_spec first hf).1
      have hilow : SourceOne.PublicCodes.lowCheckCode input = true := by
        simpa only [lowCheckCode_zero] using hi.1
      have hv : SourceOne.PublicCodes.interpretation first ≤ SourceOne.PublicCodes.interpretation input := by
        simpa only [interpretation_zero] using
          SourceOneIota.SourceAdditiveTracking.Assignment.execute_all_bounds input _ ho first List.mem_cons_self
      have hm := (SourceOne.HeightBoundary.canonicalHeightCode_le_iff_endpoint _ first hflow).mpr
        (hv.trans_lt ((SourceOne.HeightBoundary.canonicalHeightCode_le_iff_endpoint _ input hilow).mp le_rfl))
      have hb := EvaluationComponentReferenceLength.tracking_length_le_firstCode _ hp
      simp only [List.map_cons, List.length_cons, List.length_map, firstCode,
        List.head?_cons, Option.getD_some, source_one_raw_height first hf] at hb
      exact hb.trans (Nat.add_le_add_right hm 1)

theorem positive_assignment_length (s input : Nat) (word : List Nat)
    (ho : word ∈ NativeContext.SourceAdditiveTracking.Assignment.execute
      (NativePublicBridge.contextCode s) input) :
    word.length ≤ NativeContext.CanonicalHeight.canonicalHeightCode
      (NativePublicBridge.contextCode s) input + 1 := by
  let q := NativePublicBridge.contextCode s
  have ht := NativeContext.SourceAdditiveTracking.Assignment.execute_tracking q input word ho
  have hp := GlobalAdditiveTracking.RelativeCertificate.native_tracking s word ht
  have hi := (NativeContext.SourceAdditiveTracking.Assignment.inputCheck_exact q input).mp
    (NativeContext.SourceAdditiveTracking.Assignment.execute_spec q input word ho).1
  cases word with
  | nil => exact False.elim (NativeContext.SourceAdditiveTracking.Assignment.execute_nonempty q input [] ho rfl)
  | cons first rest =>
    cases rest with
    | nil => simp only [List.length_singleton]; omega
    | cons next rest =>
      have hr := (NativeContext.SourceTrackingRaw.trackingCheck_conditions q _).mp ht
      have hf : NativeContext.SourceTrackingRaw.Support.inputCheck q first = true := by
        apply hr.2.1.nodes first
        rw [stripLast_cons_nonempty first (next :: rest) (List.cons_ne_nil _ _)]
        exact List.mem_cons_self
      have hm := SourceOneIota.Mu.HeightSupport.canonicalHeightCode_mono_low q first input
        (NativeContext.SourceTrackingRaw.Support.rootCode_spec q first hf).1 hi.1
        ((NativeContext.SourceAdditiveTracking.Assignment.execute_spec q input _ ho).2.1.2.1 first List.mem_cons_self)
      have hb := EvaluationComponentReferenceLength.tracking_length_le_firstCode _ hp
      simp only [List.map_cons, List.length_cons, List.length_map, firstCode,
        List.head?_cons, Option.getD_some, MuPublicDictionary.Agreement.positivePublicCode,
        SkPublicDictionary.PositiveAgreement.publicCode, positive_raw_height s first hf] at hb
      exact hb.trans (Nat.add_le_add_right hm 1)

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationOriginalSourceLength
