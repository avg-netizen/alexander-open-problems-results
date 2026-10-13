import Alexander313.Wilken.SourceOneNativeTrackingRawSupport
import Alexander313.Wilken.PublicEpsilonNativeTrackingSequences

/-!
# Finite tracking recognition in the ORIGINAL source-one raw dictionary

Every prefix entry uses its ORIGINAL raw LOW spelling. The actual source-zero
last-atom parser and proved same-source mu spelling theorem give its genuine
mu value. The finite Boolean recurrence recognizes strict epsilon prefixes
and real mu covering. The original final principal code remains unchanged.
Both source3.17 erasure directions use concrete original unit/omega codes.
No Native base-one parser, tracking evaluation, ts assignment or resemblance
oracle is supplied. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceTrackingRaw

open Support
open NativeContext.SourceTrackingSequences (lastCode lastCode_primrec lastCode_mem
  lastCode_singleton lastCode_append_singleton stripLast_singleton stripLast_append_singleton
  list_isEmpty_primrec)
open Hereditary.FinePredecessor (stripLast stripLast_primrec stripLast_split)

def adjacencyCheck (a b : Nat) : Bool := Theta.Normalization.lessRawCode 0 a b && coverCheck a b

theorem adjacencyCheck_primrec : Primrec₂ adjacencyCheck :=
  (Primrec.and.comp (Theta.Normalization.Effective.lessRawCode_primrec.comp
    ((Primrec.const 0).pair (Primrec.fst.pair Primrec.snd))) coverCheck_primrec).to₂

abbrev ReferenceState := Option Nat × Bool

def referenceStep (a : Nat) (state : ReferenceState) : ReferenceState :=
  (some a, (Support.inputCheck a && state.2) &&
    Option.casesOn state.1 true (fun b => adjacencyCheck a b))

theorem referenceStep_primrec : Primrec₂ referenceStep := by
  have hnext : Primrec₂ (fun p : Nat × ReferenceState => fun b : Nat => adjacencyCheck p.1 b) :=
    (adjacencyCheck_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  have hmore := Primrec.option_casesOn (Primrec.fst.comp Primrec.snd) (Primrec.const true) hnext
  exact ((Primrec.option_some.comp Primrec.fst).pair
    (Primrec.and.comp (Primrec.and.comp (Support.inputCheck_primrec.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)) hmore)).to₂

def referenceRun (xs : List Nat) : ReferenceState :=
  xs.foldr (fun a state => referenceStep a state) (none, true)

theorem referenceRun_primrec : Primrec referenceRun := by
  have hs : Primrec₂ (fun _ : List Nat => fun p : Nat × ReferenceState => referenceStep p.1 p.2) :=
    (Primrec.comp referenceStep_primrec Primrec.snd).to₂
  exact Primrec.list_foldr Primrec.id (Primrec.const (none, true)) hs

theorem referenceRun_head (xs : List Nat) : (referenceRun xs).1 = xs.head? := by
  cases xs <;> rfl

def referenceCheck (xs : List Nat) : Bool := (referenceRun xs).2

theorem referenceCheck_primrec : Primrec referenceCheck := Primrec.snd.comp referenceRun_primrec

@[simp] theorem referenceCheck_nil : referenceCheck [] = true := rfl

theorem referenceCheck_cons (a : Nat) (xs : List Nat) :
    referenceCheck (a :: xs) = (Support.inputCheck a && referenceCheck xs) &&
      Option.casesOn xs.head? true (fun b => adjacencyCheck a b) := by
  change (Support.inputCheck a && referenceCheck xs) &&
    Option.casesOn (referenceRun xs).1 true (fun b => adjacencyCheck a b) = _
  rw [referenceRun_head]

/-- The actual original raw epsilon, strict-order and genuine mu-cover
conditions for a source-one reference prefix. -/
inductive Reference : List Nat → Prop
  | nil : Reference []
  | one (a : Nat) (ha : Support.inputCheck a = true) : Reference [a]
  | cons (a b : Nat) (xs : List Nat) (ha : Support.inputCheck a = true)
      (hab : interpretation 0 a < interpretation 0 b)
      (hcover : interpretation 0 b ≤ muValue a) (tail : Reference (b :: xs)) :
      Reference (a :: b :: xs)

theorem Reference.first {a : Nat} {xs : List Nat} (h : Reference (a :: xs)) :
    Support.inputCheck a = true := by
  cases h with
  | one a ha => exact ha
  | cons a b xs ha hab hc tail => exact ha

theorem Reference.nodes {xs : List Nat} (h : Reference xs) :
    ∀ c ∈ xs, Support.inputCheck c = true := by
  induction h with
  | nil => intro c hc; exact False.elim (List.not_mem_nil hc)
  | one a ha => intro c hc; simpa only [List.mem_singleton.mp hc] using ha
  | cons a b xs ha hab hc tail ih =>
    intro c hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ha
    · exact ih c hm

theorem referenceCheck_exact (xs : List Nat) : referenceCheck xs = true ↔ Reference xs := by
  induction xs with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons a xs ih =>
    cases xs with
    | nil =>
      rw [referenceCheck_cons]
      change (Support.inputCheck a && true) && true = true ↔ Reference [a]
      simp only [Bool.and_true]
      exact ⟨fun ha => .one a ha, fun h => h.first⟩
    | cons b xs =>
      rw [referenceCheck_cons]
      change (Support.inputCheck a && referenceCheck (b :: xs)) && adjacencyCheck a b = true ↔ _
      rw [Bool.and_eq_true, Bool.and_eq_true]
      constructor
      · rintro ⟨⟨ha, ht⟩, hadj⟩
        have tail := ih.mp ht
        have hb := tail.first
        have hs := Bool.and_eq_true.mp hadj
        exact .cons a b xs ha
          ((Theta.Normalization.lessRawCode_correct 0 a b
            (original_checked a (rootCode_spec a ha).1)
            (original_checked b (rootCode_spec b hb).1)).mp hs.1)
          ((coverCheck_exact a b).mp hs.2).2.2 tail
      · intro h
        cases h with
        | cons a b xs ha hab hc tail =>
          have hb := tail.first
          exact ⟨⟨ha, ih.mpr tail⟩, Bool.and_eq_true.mpr
            ⟨(Theta.Normalization.lessRawCode_correct 0 a b
              (original_checked a (rootCode_spec a ha).1)
              (original_checked b (rootCode_spec b hb).1)).mpr hab,
              (coverCheck_exact a b).mpr ⟨ha, (rootCode_spec b hb).1, hc⟩⟩⟩

theorem Reference.strict {xs : List Nat} (h : Reference xs) :
    (xs.map (interpretation 0)).Pairwise (· < ·) := by
  induction h with
  | nil => simp
  | one a ha => simp
  | cons a b xs ha hab hc tail ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro c hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hab
    · exact hab.trans ((List.pairwise_cons.mp ih).1 c hm)

theorem Reference.epsilons {xs : List Nat} (h : Reference xs) :
    ∀ c ∈ xs, lowCheckCode 0 c = true ∧ 1 < interpretation 0 c ∧
      Ordinal.omega0 ^ interpretation 0 c = interpretation 0 c ∧
        interpretation 0 c < finiteBase 1 := by
  intro c hc
  have hs := (Support.inputCheck_exact c).mp (h.nodes c hc)
  exact ⟨hs.1, hs.2.1, hs.2.2, original_bound c hs.1⟩

theorem Reference.cover {a b : Nat} {xs : List Nat} (h : Reference (a :: b :: xs)) :
    interpretation 0 b ≤ muValue a := by
  cases h with
  | cons a b xs ha hab hc tail => exact hc

def unitCode : Nat := OmegaPowers.numeralAt 0 1

theorem unitCode_spec : lowCheckCode 0 unitCode = true ∧ interpretation 0 unitCode = 1 :=
  ⟨OmegaPowers.numeralAt_checked 0 1, by simpa only [Nat.cast_one] using OmegaPowers.numeralAt_value 0 1⟩

def omegaCode : Nat := OmegaQuotient.lowPowerCode unitCode

theorem omegaCode_spec : lowCheckCode 0 omegaCode = true ∧ interpretation 0 omegaCode = Ordinal.omega0 := by
  have hs := OmegaQuotient.lowPowerCode_spec unitCode unitCode_spec.1
  exact ⟨((Theta.acceptedLowCode_iff 0 _).mp hs.1).1,
    by rw [hs.2, unitCode_spec.2, Ordinal.opow_one]⟩

def aboveOneCheck (c : Nat) : Bool := lowCheckCode 0 c && Theta.Normalization.lessRawCode 0 unitCode c

theorem aboveOneCheck_primrec : Primrec aboveOneCheck :=
  Primrec.and.comp (Uniform.hereditaryLowCheckCode_primrec.comp (Primrec.const 0) Primrec.id)
    (Theta.Normalization.Effective.lessRawCode_primrec.comp
      ((Primrec.const 0).pair ((Primrec.const unitCode).pair Primrec.id)))

theorem aboveOneCheck_exact (c : Nat) : aboveOneCheck c = true ↔
    lowCheckCode 0 c = true ∧ 1 < interpretation 0 c := by
  rw [aboveOneCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, he⟩
    exact ⟨hc, by simpa only [unitCode_spec.2] using
      (Theta.Normalization.lessRawCode_correct 0 _ c
        (original_checked _ unitCode_spec.1) (original_checked c hc)).mp he⟩
  · rintro ⟨hc, he⟩
    exact ⟨hc, (Theta.Normalization.lessRawCode_correct 0 _ c
      (original_checked _ unitCode_spec.1) (original_checked c hc)).mpr
        (by simpa only [unitCode_spec.2] using he)⟩

def trackingCheck (xs : List Nat) : Bool := !xs.isEmpty &&
  (referenceCheck (stripLast xs) && (principalCheck (lastCode xs) &&
    cond (stripLast xs).isEmpty true
      (aboveOneCheck (lastCode xs) && coverCheck (lastCode (stripLast xs)) (lastCode xs))))

/-- Exactly Definition3.16 at the ORIGINAL source-one dictionary, including
all raw epsilon prefix spellings and the unchanged raw final principal. -/
noncomputable def Tracking (xs : List Nat) : Prop := xs ≠ [] ∧ Reference (stripLast xs) ∧
  lowCheckCode 0 (lastCode xs) = true ∧ 0 < interpretation 0 (lastCode xs) ∧
    Ordinal.IsPrincipal (· + ·) (interpretation 0 (lastCode xs)) ∧
    if stripLast xs = [] then 1 ≤ interpretation 0 (lastCode xs)
    else 1 < interpretation 0 (lastCode xs) ∧
      interpretation 0 (lastCode xs) ≤ muValue (lastCode (stripLast xs))

theorem trackingCheck_primrec : Primrec trackingCheck := by
  have hp := stripLast_primrec
  have hl := lastCode_primrec
  have hpl := lastCode_primrec.comp hp
  have hf := (list_isEmpty_primrec.comp hp).cond (Primrec.const true)
    (Primrec.and.comp (aboveOneCheck_primrec.comp hl) (coverCheck_primrec.comp hpl hl))
  exact Primrec.and.comp (Primrec.not.comp list_isEmpty_primrec)
    (Primrec.and.comp (referenceCheck_primrec.comp hp)
      (Primrec.and.comp (principalCheck_primrec.comp hl) hf))

theorem trackingCheck_exact (xs : List Nat) : trackingCheck xs = true ↔ Tracking xs := by
  constructor
  · intro ht
    have h := Bool.and_eq_true.mp ht
    have hne : xs ≠ [] := by
      intro he
      have hb := h.1
      simp only [he, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true] at hb
    have hr := Bool.and_eq_true.mp h.2
    have hf := Bool.and_eq_true.mp hr.2
    have hp := (principalCheck_exact _).mp hf.1
    refine ⟨hne, (referenceCheck_exact _).mp hr.1, hp.1, hp.2.1, hp.2.2, ?_⟩
    by_cases he : stripLast xs = []
    · rw [if_pos he]
      exact Order.one_le_iff_pos.mpr hp.2.1
    · rw [if_neg he]
      have hempty : (stripLast xs).isEmpty = false := by cases hs : stripLast xs <;> simp_all
      have hc : aboveOneCheck (lastCode xs) && coverCheck (lastCode (stripLast xs)) (lastCode xs) = true := by
        simpa only [hempty, Bool.cond_false] using hf.2
      have hb := Bool.and_eq_true.mp hc
      exact ⟨((aboveOneCheck_exact _).mp hb.1).2, ((coverCheck_exact _ _).mp hb.2).2.2⟩
  · rintro ⟨hne, hr, hl, hp, hprincipal, hb⟩
    have hi : xs.isEmpty = false := by cases hs : xs <;> simp_all
    apply Bool.and_eq_true.mpr
    refine ⟨by rw [hi]; rfl, Bool.and_eq_true.mpr
      ⟨(referenceCheck_exact _).mpr hr, Bool.and_eq_true.mpr
        ⟨(principalCheck_exact _).mpr ⟨hl, hp, hprincipal⟩, ?_⟩⟩⟩
    by_cases he : stripLast xs = []
    · simp only [he, List.isEmpty_nil, Bool.cond_true]
    · have hempty : (stripLast xs).isEmpty = false := by cases hs : stripLast xs <;> simp_all
      have hbound : 1 < interpretation 0 (lastCode xs) ∧
          interpretation 0 (lastCode xs) ≤ muValue (lastCode (stripLast xs)) := by
        simpa only [if_neg he] using hb
      have hroot := hr.nodes _ (lastCode_mem (stripLast xs) he)
      simpa only [hempty, Bool.cond_false] using Bool.and_eq_true.mpr
        ⟨(aboveOneCheck_exact _).mpr ⟨hl, hbound.1⟩,
          (coverCheck_exact _ _).mpr ⟨hroot, hl, hbound.2⟩⟩

theorem tracking_erasure (xs : List Nat) (h : trackingCheck xs = true) :
    referenceCheck (stripLast xs) = true :=
  (referenceCheck_exact _).mpr ((trackingCheck_exact xs).mp h).2.1

theorem empty_reference_extension : Tracking [unitCode] := by
  refine ⟨by simp, Reference.nil, ?_, ?_, ?_, ?_⟩
  · simpa only [lastCode_singleton] using unitCode_spec.1
  · simp only [lastCode_singleton, unitCode_spec.2, zero_lt_one]
  · simpa only [lastCode_singleton, unitCode_spec.2] using Ordinal.isPrincipal_add_one
  · simp only [stripLast_singleton, if_pos rfl, lastCode_singleton, unitCode_spec.2, le_refl]

theorem nonempty_reference_extension (xs : List Nat) (h : Reference xs) (hne : xs ≠ []) :
    Tracking (xs ++ [omegaCode]) := by
  have hr := h.nodes _ (lastCode_mem xs hne)
  have hp : Ordinal.IsPrincipal (· + ·) Ordinal.omega0 := by
    simpa only [Ordinal.opow_one] using Ordinal.isPrincipal_add_omega0_opow (1 : Ordinal.{0})
  refine ⟨by simp, by simpa only [stripLast_append_singleton] using h, ?_, ?_, ?_, ?_⟩
  · simpa only [lastCode_append_singleton] using omegaCode_spec.1
  · simpa only [lastCode_append_singleton, omegaCode_spec.2] using Ordinal.omega0_pos
  · simpa only [lastCode_append_singleton, omegaCode_spec.2] using hp
  · rw [stripLast_append_singleton, if_neg hne, lastCode_append_singleton]
    exact ⟨by rw [omegaCode_spec.2]; exact Ordinal.one_lt_omega0,
      by rw [omegaCode_spec.2]; exact omega_le_muValue _ hr⟩

/-- Both Definition3.17 erasure directions are constructed from actual
original source-one unit/omega extensions and genuine mu coverage. -/
theorem reference_erasure_iff (xs : List Nat) : referenceCheck xs = true ↔
    ∃ ys, trackingCheck ys = true ∧ stripLast ys = xs := by
  constructor
  · intro hc
    have hr := (referenceCheck_exact xs).mp hc
    by_cases he : xs = []
    · subst xs
      exact ⟨[unitCode], (trackingCheck_exact _).mpr empty_reference_extension, rfl⟩
    · exact ⟨xs ++ [omegaCode], (trackingCheck_exact _).mpr (nonempty_reference_extension xs hr he),
        stripLast_append_singleton _ _⟩
  · rintro ⟨ys, hy, he⟩
    simpa only [he] using tracking_erasure ys hy

theorem Tracking.prefix_strict {xs : List Nat} (h : Tracking xs) :
    ((stripLast xs).map (interpretation 0)).Pairwise (· < ·) := h.2.1.strict

theorem Tracking.prefix_epsilons {xs : List Nat} (h : Tracking xs) :
    ∀ c ∈ stripLast xs, 1 < interpretation 0 c ∧
      Ordinal.omega0 ^ interpretation 0 c = interpretation 0 c := by
  intro c hc
  have hs := h.2.1.epsilons c hc
  exact ⟨hs.2.1, hs.2.2.1⟩

theorem Tracking.source_domain {xs : List Nat} (h : Tracking xs) :
    ∀ c ∈ xs, lowCheckCode 0 c = true ∧ interpretation 0 c < finiteBase 1 := by
  obtain ⟨a, he, hh⟩ := stripLast_split xs h.1
  have hlast : lastCode xs = a := by
    simp only [NativeContext.SourceTrackingSequences.lastCode, hh, Option.getD_some]
  have hs : xs = stripLast xs ++ [lastCode xs] := by simpa only [hlast] using he
  intro c hc
  rw [hs] at hc
  rcases List.mem_append.mp hc with hc | hc
  · have hl := (rootCode_spec c (h.2.1.nodes c hc)).1
    exact ⟨hl, original_bound c hl⟩
  · have heq := List.mem_singleton.mp hc
    subst c
    exact ⟨h.2.2.1, original_bound _ h.2.2.1⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceTrackingRaw
