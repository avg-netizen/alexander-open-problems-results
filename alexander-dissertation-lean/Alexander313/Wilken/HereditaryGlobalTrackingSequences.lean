import Alexander313.Wilken.HereditaryGlobalTrackingSequencesRecognitionSupport

/-!
# Exact primitive recursive recognition of finite global RS and TS

The bounded scan checks an actual initial upsilon chain and its genuine
open endpoint gap, followed by the independently checked epsilon tail.
The final principal entry has the printed empty-prefix bound or the true
extended-mu cover. These checks recognize the independently defined
Definition3.18 predicates, without an assignment or evaluation oracle.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalTrackingSequences

open GlobalAdditiveTracking.Source (baseWord baseWord_primrec)
open RecognitionSupport
open Hereditary.FinePredecessor (stripLast stripLast_primrec)
open NativeContext.SourceTrackingSequences (lastCode lastCode_primrec lastCode_mem)
open NativeContext.SourceTrackingSequences.Support (canonical_not_less_exact)

def segmentCheck (codes : List Nat) (m : Nat) : Bool :=
  (codes.take m == baseWord m) &&
    (epsilonCheck (codes.drop m) && tailGapCheck m (codes.drop m))

theorem segmentCheck_primrec : Primrec₂ segmentCheck := by
  have htake := Primrec.list_take.comp Primrec.snd Primrec.fst
  have hdrop := Primrec.list_drop.comp Primrec.snd Primrec.fst
  have hbase := baseWord_primrec.comp Primrec.snd
  exact (Primrec.and.comp (Primrec.beq.comp htake hbase)
    (Primrec.and.comp (epsilonCheck_primrec.comp hdrop)
      (tailGapCheck_primrec.comp Primrec.snd hdrop))).to₂

theorem segmentCheck_exact (codes : List Nat) (m : Nat) : segmentCheck codes m = true ↔
    codes.take m = baseWord m ∧ EpsilonReference (codes.drop m) ∧ TailGap m (codes.drop m) := by
  rw [segmentCheck, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨htake, heps, hgap⟩
    have hr := (epsilonCheck_exact _).mp heps
    exact ⟨htake, hr, (tailGapCheck_exact _ _ hr).mp hgap⟩
  · rintro ⟨htake, hr, hg⟩
    exact ⟨htake, (epsilonCheck_exact _).mpr hr, (tailGapCheck_exact _ _ hr).mpr hg⟩

/-- Every possible finite initial endpoint chain is examined, including
the empty chain. Its length bound follows from the actual decomposition. -/
def referenceCheck (codes : List Nat) : Bool :=
  (List.range (codes.length + 1)).any (segmentCheck codes)

theorem referenceCheck_primrec : Primrec referenceCheck :=
  (SourceOne.Comparison.Effective.listAny_primrec segmentCheck segmentCheck_primrec).comp
    Primrec.id (Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length))

theorem referenceCheck_exact (codes : List Nat) : referenceCheck codes = true ↔ Reference codes := by
  rw [referenceCheck, List.any_eq_true]
  constructor
  · rintro ⟨m, hm, hcheck⟩
    have hs := (segmentCheck_exact codes m).mp hcheck
    refine ⟨m, codes.drop m, ?_, hs.2⟩
    rw [← hs.1]
    exact (List.take_append_drop m codes).symm
  · rintro ⟨m, tail, he, hr, hg⟩
    have hm : m ≤ codes.length := by
      rw [he, List.length_append, baseWord_length]
      omega
    have htake : codes.take m = baseWord m := by
      rw [he]
      exact List.take_left' (baseWord_length m)
    have hdrop : codes.drop m = tail := by
      rw [he]
      exact List.drop_left' (baseWord_length m)
    refine ⟨m, List.mem_range.mpr (by omega), (segmentCheck_exact codes m).mpr ?_⟩
    exact ⟨htake, hdrop.symm ▸ hr, hdrop.symm ▸ hg⟩

theorem referenceCheck_baseWord (m : Nat) : referenceCheck (baseWord m) = true :=
  (referenceCheck_exact _).mpr (reference_baseWord m)

theorem referenceCheck_epsilon (codes : List Nat) (hr : referenceCheck codes = true) :
    ∀ c ∈ codes, GlobalMuDictionary.Support.inputCheck c = true :=
  fun c hc => (GlobalMuDictionary.Support.inputCheck_exact c).mpr
    (((referenceCheck_exact codes).mp hr).epsilons c hc)

def atMostFirstEndpointCheck (c : Nat) : Bool := Canonical.check c &&
  !(Canonical.less (endpointCode 1) c)

theorem atMostFirstEndpointCheck_primrec : Primrec atMostFirstEndpointCheck :=
  Primrec.and.comp Canonical.Effective.check_primrec
    (Primrec.not.comp (Canonical.Effective.less_primrec.comp (Primrec.const _) Primrec.id))

theorem atMostFirstEndpointCheck_exact (c : Nat) : atMostFirstEndpointCheck c = true ↔
    Canonical.check c = true ∧ unionInterpretation c ≤ sourceUpsilon (1 : Ordinal.{0}) := by
  rw [atMostFirstEndpointCheck, Bool.and_eq_true]
  have hv : unionInterpretation (endpointCode 1) = sourceUpsilon (1 : Ordinal.{0}) :=
    (PublicEpsilonSourceDictionary.endpointCode_value 1).trans
      (PublicUpsilonSegment.successor_value 0).symm
  constructor
  · rintro ⟨hc, hb⟩
    exact ⟨hc, by rw [← hv]; exact
      (canonical_not_less_exact _ _ (PublicEpsilonSourceDictionary.endpointCode_checked 1) hc).mp hb⟩
  · rintro ⟨hc, hb⟩
    exact ⟨hc, (canonical_not_less_exact _ _
      (PublicEpsilonSourceDictionary.endpointCode_checked 1) hc).mpr (by
        rw [hv]; exact hb)⟩

def trackingCheck (codes : List Nat) : Bool := !codes.isEmpty &&
  (PublicTrackingSequences.canonicalWordCheck codes &&
    (referenceCheck (stripLast codes) && (PublicTrackingSequences.principalCheck (lastCode codes) &&
      cond (stripLast codes).isEmpty
        (PublicTrackingSequences.atLeastOneCheck (lastCode codes) && atMostFirstEndpointCheck (lastCode codes))
        (PublicTrackingSequences.aboveOneCheck (lastCode codes) &&
          coverCheck (lastCode (stripLast codes)) (lastCode codes)))))

theorem trackingCheck_primrec : Primrec trackingCheck := by
  have hp := stripLast_primrec
  have hl := lastCode_primrec
  have hpl := lastCode_primrec.comp hp
  have hcover := coverCheck_primrec.comp hpl hl
  have hfirst := Primrec.and.comp (PublicTrackingSequences.atLeastOneCheck_primrec.comp hl)
    (atMostFirstEndpointCheck_primrec.comp hl)
  have hfinal := (NativeContext.SourceTrackingSequences.list_isEmpty_primrec.comp hp).cond
    hfirst (Primrec.and.comp (PublicTrackingSequences.aboveOneCheck_primrec.comp hl) hcover)
  exact Primrec.and.comp (Primrec.not.comp NativeContext.SourceTrackingSequences.list_isEmpty_primrec)
    (Primrec.and.comp PublicTrackingSequences.canonicalWordCheck_primrec
      (Primrec.and.comp (referenceCheck_primrec.comp hp)
        (Primrec.and.comp (PublicTrackingSequences.principalCheck_primrec.comp hl) hfinal)))

theorem trackingCheck_exact (codes : List Nat) : trackingCheck codes = true ↔ Tracking codes := by
  constructor
  · intro ht
    have h := Bool.and_eq_true.mp ht
    have hne : codes ≠ [] := by
      intro he
      have hb := h.1
      simp only [he, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true] at hb
    have hall := Bool.and_eq_true.mp h.2
    have hr := Bool.and_eq_true.mp hall.2
    have hf := Bool.and_eq_true.mp hr.2
    have hp := (PublicTrackingSequences.principalCheck_exact _).mp hf.1
    refine ⟨hne, (PublicTrackingSequences.canonicalWordCheck_exact _).mp hall.1,
      (referenceCheck_exact _).mp hr.1, hp.2.1, hp.2.2, ?_⟩
    by_cases he : stripLast codes = []
    · rw [if_pos he]
      have hc : PublicTrackingSequences.atLeastOneCheck (lastCode codes) &&
          atMostFirstEndpointCheck (lastCode codes) = true := by
        simpa only [he, List.isEmpty_nil, Bool.cond_true] using hf.2
      have hb := Bool.and_eq_true.mp hc
      exact ⟨((PublicTrackingSequences.atLeastOneCheck_exact _).mp hb.1).2,
        ((atMostFirstEndpointCheck_exact _).mp hb.2).2⟩
    · rw [if_neg he]
      have hi : (stripLast codes).isEmpty = false := by
        cases hs : stripLast codes <;> simp_all
      have hc : PublicTrackingSequences.aboveOneCheck (lastCode codes) &&
          coverCheck (lastCode (stripLast codes)) (lastCode codes) = true := by
        simpa only [hi, Bool.cond_false] using hf.2
      have hb := Bool.and_eq_true.mp hc
      exact ⟨((PublicTrackingSequences.aboveOneCheck_exact _).mp hb.1).2,
        ((coverCheck_exact _ _).mp hb.2).2.2⟩
  · rintro ⟨hne, hall, hr, hp, hprincipal, hbound⟩
    have hi : codes.isEmpty = false := by cases hs : codes <;> simp_all
    have hl := hall _ (lastCode_mem codes hne)
    apply Bool.and_eq_true.mpr
    refine ⟨by rw [hi]; rfl, Bool.and_eq_true.mpr
      ⟨(PublicTrackingSequences.canonicalWordCheck_exact _).mpr hall, Bool.and_eq_true.mpr
        ⟨(referenceCheck_exact _).mpr hr, Bool.and_eq_true.mpr
          ⟨(PublicTrackingSequences.principalCheck_exact _).mpr ⟨hl, hp, hprincipal⟩, ?_⟩⟩⟩⟩
    by_cases he : stripLast codes = []
    · have hb : 1 ≤ unionInterpretation (lastCode codes) ∧
          unionInterpretation (lastCode codes) ≤ sourceUpsilon (1 : Ordinal.{0}) := by
        simpa only [if_pos he] using hbound
      simpa only [he, List.isEmpty_nil, Bool.cond_true] using Bool.and_eq_true.mpr
        ⟨(PublicTrackingSequences.atLeastOneCheck_exact _).mpr ⟨hl, hb.1⟩,
          (atMostFirstEndpointCheck_exact _).mpr ⟨hl, hb.2⟩⟩
    · have hempty : (stripLast codes).isEmpty = false := by
        cases hs : stripLast codes <;> simp_all
      have hb : 1 < unionInterpretation (lastCode codes) ∧
          unionInterpretation (lastCode codes) ≤ muValue (lastCode (stripLast codes)) := by
        simpa only [if_neg he] using hbound
      have hroot := hr.last_mu_input he
      simpa only [hempty, Bool.cond_false] using Bool.and_eq_true.mpr
        ⟨(PublicTrackingSequences.aboveOneCheck_exact _).mpr ⟨hl, hb.1⟩,
          (coverCheck_exact _ _).mpr ⟨hroot, hl, hb.2⟩⟩

theorem trackingCheck_erasure (codes : List Nat) (ht : trackingCheck codes = true) :
    referenceCheck (stripLast codes) = true :=
  (referenceCheck_exact _).mpr ((trackingCheck_exact codes).mp ht).2.2.1

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalTrackingSequences
