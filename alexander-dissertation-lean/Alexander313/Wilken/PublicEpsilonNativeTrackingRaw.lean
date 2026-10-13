import Alexander313.Wilken.PublicEpsilonNativeTrackingRawSupport

/-!
# Finite tracking recognition with original raw epsilon spellings

Original prefix codes are retained. The actual SAME-q root-atom producer
constructs the root dictionary used by the finite reference/tracking checks;
every reconstructed value equals its ORIGINAL input value. Mu independence
has been derived from the genuine same-source mu theorem. The last principal
entry is unchanged. No source3.8, Par transport or tracking evaluation input
is supplied. All source candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceTrackingRaw

open PublicEpsilonUnboundedIota Support
open SourceTrackingSequences (lastCode lastCode_primrec lastCode_mem)
open Hereditary.FinePredecessor (stripLast stripLast_primrec)

def prefixCheck (q : Nat) (xs : List Nat) : Bool := xs.all (Support.inputCheck q)

theorem prefixCheck_primrec : Primrec₂ prefixCheck :=
  SourceOne.Comparison.Effective.listAll_primrec Support.inputCheck Support.inputCheck_primrec

theorem prefixCheck_exact (q : Nat) (xs : List Nat) : prefixCheck q xs = true ↔
    ∀ c ∈ xs, Support.inputCheck q c = true := List.all_eq_true

def referenceCheck (q : Nat) (xs : List Nat) : Bool :=
  prefixCheck q xs && SourceTrackingSequences.referenceCheck q (rootWord q xs)

theorem referenceCheck_primrec : Primrec₂ referenceCheck :=
  (Primrec.and.comp prefixCheck_primrec
    (SourceTrackingSequences.referenceCheck_primrec.comp Primrec.fst rootWord_primrec)).to₂

def Reference (q : Nat) (xs : List Nat) : Prop :=
  (∀ c ∈ xs, Support.inputCheck q c = true) ∧
    SourceTrackingSequences.Reference q (rootWord q xs)

theorem referenceCheck_exact (q : Nat) (xs : List Nat) :
    referenceCheck q xs = true ↔ Reference q xs := by
  rw [referenceCheck, Bool.and_eq_true, prefixCheck_exact,
    SourceTrackingSequences.referenceCheck_exact]
  rfl

theorem Reference.nodes {q : Nat} {xs : List Nat} (h : Reference q xs) :
    ∀ c ∈ xs, Support.inputCheck q c = true := h.1

theorem Reference.strict {q : Nat} {xs : List Nat} (h : Reference q xs) :
    (xs.map (interpretation q)).Pairwise (· < ·) := by
  rw [← rootWord_values q xs h.1]
  exact h.2.strict

theorem Reference.epsilons {q : Nat} {xs : List Nat} (h : Reference q xs) :
    ∀ c ∈ xs, lowCheckCode q c = true ∧ base q < interpretation q c ∧
      Ordinal.omega0 ^ interpretation q c = interpretation q c ∧
      interpretation q c < globalBoundary (base q) 0 := by
  intro c hc
  have hs := (Support.inputCheck_exact q c).mp (h.1 c hc)
  exact ⟨hs.1, hs.2.1, hs.2.2, checked_low_bound q c hs.1⟩

theorem original_pair_cover (q a b : Nat) (xs : List Nat)
    (h : SourceTrackingSequences.Reference q (a :: b :: xs)) :
    interpretation q b ≤ Mu.sourceValue q a := by
  cases h with
  | cons a b xs ha hab hc tail => exact hc

theorem Reference.cover {q a b : Nat} {xs : List Nat} (h : Reference q (a :: b :: xs)) :
    interpretation q b ≤ muValue q a := by
  have hs := rootCode_spec q b (h.1 b (by simp))
  have hc := original_pair_cover q (rootCode q a) (rootCode q b) (rootWord q xs) h.2
  simpa only [hs.2.2, muValue] using hc

theorem rootWord_ne_nil (q : Nat) (xs : List Nat) (hne : xs ≠ []) : rootWord q xs ≠ [] := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons c xs => simp only [rootWord_cons, List.cons_ne_nil]

theorem rootWord_lastCode (q : Nat) (xs : List Nat) (hne : xs ≠ []) :
    lastCode (rootWord q xs) = rootCode q (lastCode xs) := by
  obtain ⟨a, he, hh⟩ := Hereditary.FinePredecessor.stripLast_split xs hne
  have hl : lastCode xs = a := by
    simp only [SourceTrackingSequences.lastCode, hh, Option.getD_some]
  calc
    lastCode (rootWord q xs) = rootCode q a := by
      rw [he, rootWord, List.map_append, List.map_cons, List.map_nil,
        SourceTrackingSequences.lastCode_append_singleton]
    _ = rootCode q (lastCode xs) := congrArg (rootCode q) hl.symm

def trackingWord (q : Nat) (xs : List Nat) : List Nat :=
  rootWord q (stripLast xs) ++ [lastCode xs]

theorem trackingWord_primrec : Primrec₂ trackingWord := by
  have hp := rootWord_primrec.comp Primrec.fst (stripLast_primrec.comp Primrec.snd)
  have hl := Primrec.list_cons.comp (lastCode_primrec.comp Primrec.snd) (Primrec.const [])
  exact (Primrec.list_append.comp hp hl).to₂

theorem trackingWord_ne_nil (q : Nat) (xs : List Nat) : trackingWord q xs ≠ [] := by
  simp only [trackingWord, List.append_eq_nil_iff, List.cons_ne_nil, and_false, not_false_eq_true]

theorem trackingWord_stripLast (q : Nat) (xs : List Nat) :
    stripLast (trackingWord q xs) = rootWord q (stripLast xs) :=
  SourceTrackingSequences.stripLast_append_singleton _ _

theorem trackingWord_last (q : Nat) (xs : List Nat) : lastCode (trackingWord q xs) = lastCode xs :=
  SourceTrackingSequences.lastCode_append_singleton _ _

def trackingCheck (q : Nat) (xs : List Nat) : Bool := !xs.isEmpty &&
  (prefixCheck q (stripLast xs) && SourceTrackingSequences.trackingCheck q (trackingWord q xs))

theorem trackingCheck_primrec : Primrec₂ trackingCheck :=
  (Primrec.and.comp
    (Primrec.not.comp (SourceTrackingSequences.list_isEmpty_primrec.comp Primrec.snd))
    (Primrec.and.comp (prefixCheck_primrec.comp Primrec.fst (stripLast_primrec.comp Primrec.snd))
      (SourceTrackingSequences.trackingCheck_primrec.comp Primrec.fst trackingWord_primrec))).to₂

/-- Exactly the original raw prefix callers and the genuine same-value
root-dictionary tracking conditions. The final original principal code is
unchanged, and its concrete mu test uses a proved spelling-independent mu. -/
def Tracking (q : Nat) (xs : List Nat) : Prop := xs ≠ [] ∧
  (∀ c ∈ stripLast xs, Support.inputCheck q c = true) ∧
    SourceTrackingSequences.Tracking q (trackingWord q xs)

theorem trackingCheck_exact (q : Nat) (xs : List Nat) :
    trackingCheck q xs = true ↔ Tracking q xs := by
  rw [trackingCheck, Bool.and_eq_true, Bool.and_eq_true, prefixCheck_exact,
    SourceTrackingSequences.trackingCheck_exact]
  apply and_congr_left
  intro h
  cases xs <;> simp

theorem tracking_erasure (q : Nat) (xs : List Nat) (h : trackingCheck q xs = true) :
    referenceCheck q (stripLast xs) = true := by
  have hs := (trackingCheck_exact q xs).mp h
  apply (referenceCheck_exact q _).mpr
  refine ⟨hs.2.1, ?_⟩
  have hr := hs.2.2.2.1
  simpa only [trackingWord_stripLast] using hr

theorem Tracking.prefix_strict {q : Nat} {xs : List Nat} (h : Tracking q xs) :
    ((stripLast xs).map (interpretation q)).Pairwise (· < ·) := by
  have hr : Reference q (stripLast xs) :=
    (referenceCheck_exact q _).mp (tracking_erasure q xs ((trackingCheck_exact q xs).mpr h))
  exact hr.strict

/-- The final entry satisfies the actual original ordinal conditions,
with the unchanged raw spelling and its genuinely spelling-independent mu. -/
theorem Tracking.final_conditions {q : Nat} {xs : List Nat} (h : Tracking q xs) :
    lowCheckCode q (lastCode xs) = true ∧
      0 < interpretation q (lastCode xs) ∧
      Ordinal.IsPrincipal (· + ·) (interpretation q (lastCode xs)) ∧
      if stripLast xs = [] then base q ≤ interpretation q (lastCode xs)
      else 1 < interpretation q (lastCode xs) ∧
        interpretation q (lastCode xs) ≤ muValue q (lastCode (stripLast xs)) := by
  obtain ⟨_, hr, hl, hp, hprincipal, hb⟩ := h.2.2
  rw [trackingWord_last] at hl hp hprincipal
  rw [trackingWord_stripLast, trackingWord_last] at hb
  refine ⟨hl, hp, hprincipal, ?_⟩
  by_cases he : stripLast xs = []
  · simpa only [he, rootWord_nil, if_pos rfl] using hb
  · have hn := rootWord_ne_nil q (stripLast xs) he
    rw [if_neg he]
    rw [if_neg hn, rootWord_lastCode q (stripLast xs) he] at hb
    exact hb

/-- The raw recognizer's exact conditions are the actual source prefix
and final-entry inequalities, rather than a supplied evaluation relation. -/
theorem trackingCheck_conditions (q : Nat) (xs : List Nat) : trackingCheck q xs = true ↔
    xs ≠ [] ∧ Reference q (stripLast xs) ∧
      lowCheckCode q (lastCode xs) = true ∧
      0 < interpretation q (lastCode xs) ∧
      Ordinal.IsPrincipal (· + ·) (interpretation q (lastCode xs)) ∧
      if stripLast xs = [] then base q ≤ interpretation q (lastCode xs)
      else 1 < interpretation q (lastCode xs) ∧
        interpretation q (lastCode xs) ≤ muValue q (lastCode (stripLast xs)) := by
  constructor
  · intro hc
    have ht := (trackingCheck_exact q xs).mp hc
    exact ⟨ht.1, (referenceCheck_exact q _).mp (tracking_erasure q xs hc), ht.final_conditions⟩
  · rintro ⟨hne, hr, hl, hp, hprincipal, hb⟩
    apply (trackingCheck_exact q xs).mpr
    refine ⟨hne, hr.1, trackingWord_ne_nil q xs, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [trackingWord_stripLast] using hr.2
    · simpa only [trackingWord_last] using hl
    · simpa only [trackingWord_last] using hp
    · simpa only [trackingWord_last] using hprincipal
    · rw [trackingWord_stripLast, trackingWord_last]
      by_cases he : stripLast xs = []
      · simpa only [he, rootWord_nil, if_pos rfl] using hb
      · have hn := rootWord_ne_nil q (stripLast xs) he
        rw [if_neg he] at hb
        rw [if_neg hn, rootWord_lastCode q (stripLast xs) he]
        exact hb

theorem Tracking.source_domain {q : Nat} {xs : List Nat} (h : Tracking q xs) :
    ∀ c ∈ xs, lowCheckCode q c = true ∧ interpretation q c < globalBoundary (base q) 0 := by
  obtain ⟨a, he, hh⟩ := Hereditary.FinePredecessor.stripLast_split xs h.1
  have hlast : lastCode xs = a := by simp only [SourceTrackingSequences.lastCode, hh, Option.getD_some]
  have hs : xs = stripLast xs ++ [lastCode xs] := by simpa only [hlast] using he
  intro c hc
  rw [hs] at hc
  rcases List.mem_append.mp hc with hc | hc
  · have hl := (rootCode_spec q c (h.2.1 c hc)).1
    exact ⟨hl, checked_low_bound q c hl⟩
  · have heq : c = lastCode xs := List.mem_singleton.mp hc
    subst c
    have hl := h.2.2.2.2.1
    have hl' : lowCheckCode q (lastCode xs) = true := by
      simpa only [trackingWord_last] using hl
    exact ⟨hl', checked_low_bound q _ hl'⟩

/-- Every original raw reference prefix has a constructed genuine tracking
extension. The empty case uses the actual original base; the nonempty case
uses the actual original omega code, with its mu covering already proved. -/
theorem reference_erasure_iff (q : Nat) (hq : baseCheck q = true) (xs : List Nat) :
    referenceCheck q xs = true ↔ ∃ ys, trackingCheck q ys = true ∧ stripLast ys = xs := by
  constructor
  · intro hc
    have hs := (referenceCheck_exact q xs).mp hc
    by_cases he : xs = []
    · subst xs
      refine ⟨[SourceLocalization.baseRaw q], (trackingCheck_exact q _).mpr ?_, rfl⟩
      refine ⟨by simp, ?_, ?_⟩
      · intro c hm
        simp only [SourceTrackingSequences.stripLast_singleton, List.not_mem_nil] at hm
      · simpa only [trackingWord, SourceTrackingSequences.stripLast_singleton, rootWord_nil,
          SourceTrackingSequences.lastCode_singleton, List.nil_append] using
          SourceTrackingSequences.empty_reference_extension q hq
    · let omegaCode := OmegaPowers.powerCode q (OmegaPowerHeight.numeralCode 1)
      refine ⟨xs ++ [omegaCode], (trackingCheck_exact q _).mpr ?_,
        SourceTrackingSequences.stripLast_append_singleton _ _⟩
      refine ⟨by simp, ?_, ?_⟩
      · simpa only [SourceTrackingSequences.stripLast_append_singleton] using hs.1
      · have ht := SourceTrackingSequences.nonempty_reference_extension q (rootWord q xs)
          hs.2 (rootWord_ne_nil q xs he)
        simpa only [trackingWord, SourceTrackingSequences.stripLast_append_singleton,
          SourceTrackingSequences.lastCode_append_singleton, omegaCode] using ht
  · rintro ⟨ys, hy, he⟩
    simpa only [he] using tracking_erasure q ys hy

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceTrackingRaw
