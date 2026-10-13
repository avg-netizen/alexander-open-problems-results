import Alexander313.Wilken.PublicEpsilonNativeTrackingSequencesSupport
import Alexander313.Wilken.PublicEpsilonNativeFinePredecessor

/-!
# Original mu-covered reference sequences and finite source recognition

The prefix entries use the literal original ANY-q Normal high-root
dictionary. Each adjacent source comparison and mu covering is a genuine
finite computation. The last tracking entry is an original raw LOW
additive principal. This layer constructs the source sequence conditions;
it does not assign ts, evaluate a tracking chain or decide resemblance.
All candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceTrackingSequences

open PublicEpsilonUnboundedIota Support

def adjacencyCheck (q a b : Nat) : Bool :=
  Normalization.lessRawCode q a b && coverCheck q a b

theorem adjacencyCheck_primrec : Primrec (fun p : (Nat × Nat) × Nat =>
    adjacencyCheck p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (Normalization.Effective.lessRawCode_primrec.comp
    ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))) coverCheck_primrec

abbrev ReferenceState := Option Nat × Bool

def referenceStep (q a : Nat) (state : ReferenceState) : ReferenceState :=
  (some a, (Mu.inputCheck q a && state.2) &&
    Option.casesOn state.1 true (fun b => adjacencyCheck q a b))

theorem referenceStep_primrec : Primrec
    (fun p : (Nat × Nat) × ReferenceState => referenceStep p.1.1 p.1.2 p.2) := by
  have ha := Primrec.snd.comp Primrec.fst
  have hopt := Primrec.fst.comp Primrec.snd
  have hnext : Primrec₂ (fun p : (Nat × Nat) × ReferenceState =>
      fun b : Nat => adjacencyCheck p.1.1 p.1.2 b) :=
    (adjacencyCheck_primrec.comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  have hmore := Primrec.option_casesOn hopt (Primrec.const true) hnext
  exact (Primrec.option_some.comp ha).pair
    (Primrec.and.comp (Primrec.and.comp (Mu.inputCheck_primrec.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)) hmore)

def referenceRun (q : Nat) (xs : List Nat) : ReferenceState :=
  xs.foldr (fun a state => referenceStep q a state) (none, true)

theorem referenceRun_primrec : Primrec₂ referenceRun := by
  have hstep : Primrec₂ (fun p : Nat × List Nat =>
      fun s : Nat × ReferenceState => referenceStep p.1 s.1 s.2) :=
    (referenceStep_primrec.comp
      (((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd))).to₂
  exact (Primrec.list_foldr Primrec.snd (Primrec.const (none, true)) hstep).to₂

theorem referenceRun_head (q : Nat) (xs : List Nat) : (referenceRun q xs).1 = xs.head? := by
  cases xs <;> rfl

def referenceCheck (q : Nat) (xs : List Nat) : Bool := (referenceRun q xs).2

theorem referenceCheck_primrec : Primrec₂ referenceCheck :=
  (Primrec.snd.comp referenceRun_primrec).to₂

@[simp] theorem referenceCheck_nil (q : Nat) : referenceCheck q [] = true := rfl

theorem referenceCheck_cons (q a : Nat) (xs : List Nat) :
    referenceCheck q (a :: xs) = (Mu.inputCheck q a && referenceCheck q xs) &&
      Option.casesOn xs.head? true (fun b => adjacencyCheck q a b) := by
  change (Mu.inputCheck q a && referenceCheck q xs) &&
    Option.casesOn (referenceRun q xs).1 true (fun b => adjacencyCheck q a b) = _
  rw [referenceRun_head]

/-- The actual original-root dictionary for the printed strictly
increasing, epsilon, mu-covered reference prefix. Covering compares real
ordinals in their different contexts, never the numerical codes. -/
inductive Reference (q : Nat) : List Nat → Prop
  | nil : Reference q []
  | one (a : Nat) (ha : Mu.inputCheck q a = true) : Reference q [a]
  | cons (a b : Nat) (xs : List Nat) (ha : Mu.inputCheck q a = true)
      (hab : interpretation q a < interpretation q b)
      (hcover : interpretation q b ≤ Mu.sourceValue q a)
      (tail : Reference q (b :: xs)) : Reference q (a :: b :: xs)

theorem Reference.first {q a : Nat} {xs : List Nat} (h : Reference q (a :: xs)) :
    Mu.inputCheck q a = true := by
  cases h with
  | one a ha => exact ha
  | cons a b xs ha hab hcover tail => exact ha

theorem Reference.nodes {q : Nat} {xs : List Nat} (h : Reference q xs) :
    ∀ a ∈ xs, Mu.inputCheck q a = true := by
  induction h with
  | nil => intro a ha; exact False.elim (List.not_mem_nil ha)
  | one a ha => intro b hb; simpa only [List.mem_singleton.mp hb] using ha
  | cons a b xs ha hab hcover tail ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ha
    · exact ih c hc

theorem referenceCheck_exact (q : Nat) (xs : List Nat) :
    referenceCheck q xs = true ↔ Reference q xs := by
  induction xs with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons a xs ih =>
    cases xs with
    | nil =>
      rw [referenceCheck_cons]
      change (Mu.inputCheck q a && true) && true = true ↔ Reference q [a]
      simp only [Bool.and_true]
      exact ⟨fun ha => .one a ha, fun h => h.first⟩
    | cons b xs =>
      rw [referenceCheck_cons]
      change (Mu.inputCheck q a && referenceCheck q (b :: xs)) && adjacencyCheck q a b = true ↔ _
      rw [Bool.and_eq_true, Bool.and_eq_true]
      constructor
      · rintro ⟨⟨ha, ht⟩, hadj⟩
        have tail := ih.mp ht
        have hs := Bool.and_eq_true.mp hadj
        exact .cons a b xs ha ((Normalization.lessRawCode_exact q a b).mp hs.1).2.2
          ((coverCheck_exact q a b).mp hs.2).2.2 tail
      · intro h
        cases h with
        | cons a b xs ha hab hcover tail =>
          have hb := tail.first
          exact ⟨⟨ha, ih.mpr tail⟩, Bool.and_eq_true.mpr
            ⟨(Normalization.lessRawCode_exact q a b).mpr
              ⟨RootLowCollapse.root_original q a ha, RootLowCollapse.root_original q b hb, hab⟩,
              (coverCheck_exact q a b).mpr ⟨ha, RootLowCollapse.root_low q b hb, hcover⟩⟩⟩

theorem Reference.strict {q : Nat} {xs : List Nat} (h : Reference q xs) :
    (xs.map (interpretation q)).Pairwise (· < ·) := by
  induction h with
  | nil => simp
  | one a ha => simp
  | cons a b xs ha hab hcover tail ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hab
    · exact hab.trans ((List.pairwise_cons.mp ih).1 c hc)

theorem Reference.epsilons {q : Nat} {xs : List Nat} (h : Reference q xs) :
    ∀ a ∈ xs, base q < interpretation q a ∧
      Ordinal.omega0 ^ interpretation q a = interpretation q a ∧
      interpretation q a < globalBoundary (base q) 0 := by
  intro a ha
  have hc := h.nodes a ha
  exact ⟨Mu.root_base_lt q a hc, RootLowCollapse.root_epsilon q a hc,
    checked_low_bound q a (RootLowCollapse.root_low q a hc)⟩

theorem raw_not_less_exact (q a b : Nat) (ha : checkCode q a = true)
    (hb : checkCode q b = true) : !(Normalization.lessRawCode q a b) = true ↔
      interpretation q b ≤ interpretation q a := by
  constructor
  · intro h
    apply le_of_not_gt
    intro hlt
    have hl := (Normalization.lessRawCode_exact q a b).mpr ⟨ha, hb, hlt⟩
    simp only [hl, Bool.not_true, Bool.false_eq_true] at h
  · intro hle
    cases h : Normalization.lessRawCode q a b with
    | false => rfl
    | true => exact False.elim (((Normalization.lessRawCode_exact q a b).mp h).2.2.not_ge hle)

def atLeastBaseCheck (q c : Nat) : Bool := lowCheckCode q c &&
  !(Normalization.lessRawCode q c (SourceLocalization.baseRaw q))

theorem atLeastBaseCheck_primrec : Primrec₂ atLeastBaseCheck :=
  (Primrec.and.comp lowCheckCode_primrec
    (Primrec.not.comp (Normalization.Effective.lessRawCode_primrec.comp
      (Primrec.fst.pair (Primrec.snd.pair
        (SourceLocalization.baseRaw_primrec.comp Primrec.fst)))))).to₂

theorem atLeastBaseCheck_exact (q c : Nat) : atLeastBaseCheck q c = true ↔
    lowCheckCode q c = true ∧ base q ≤ interpretation q c := by
  rw [atLeastBaseCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, hle⟩
    have hq := (HeightBoundary.input_spec q c hc).2.1
    have hb := (Comparison.acceptedCode_exact q _).mp
      (SourceLocalization.node_accepted q _ (SourceLocalization.baseRaw_node q hq))
    have hp := (raw_not_less_exact q c _ (Bool.and_eq_true.mp hc).1 hb.1).mp hle
    exact ⟨hc, by simpa only [← SourceLocalization.value,
      SourceLocalization.baseRaw_value q hq] using hp⟩
  · rintro ⟨hc, hle⟩
    have hq := (HeightBoundary.input_spec q c hc).2.1
    have hb := (Comparison.acceptedCode_exact q _).mp
      (SourceLocalization.node_accepted q _ (SourceLocalization.baseRaw_node q hq))
    exact ⟨hc, (raw_not_less_exact q c _ (Bool.and_eq_true.mp hc).1 hb.1).mpr
      (by simpa only [← SourceLocalization.value,
        SourceLocalization.baseRaw_value q hq] using hle)⟩

def aboveOneCheck (q c : Nat) : Bool := lowCheckCode q c &&
  Normalization.lessRawCode q LogEndZero.unitCode c

theorem aboveOneCheck_primrec : Primrec₂ aboveOneCheck :=
  (Primrec.and.comp lowCheckCode_primrec
    (Normalization.Effective.lessRawCode_primrec.comp
      (Primrec.fst.pair ((Primrec.const LogEndZero.unitCode).pair Primrec.snd)))).to₂

theorem aboveOneCheck_exact (q c : Nat) : aboveOneCheck q c = true ↔
    lowCheckCode q c = true ∧ 1 < interpretation q c := by
  rw [aboveOneCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, hlt⟩
    exact ⟨hc, by simpa only [LogEndZero.unitCode_value q] using
      ((Normalization.lessRawCode_exact q LogEndZero.unitCode c).mp hlt).2.2⟩
  · rintro ⟨hc, hlt⟩
    have hq := (HeightBoundary.input_spec q c hc).2.1
    have hu := (Comparison.acceptedCode_exact q _).mp (LogEndZero.unitCode_accepted q hq)
    exact ⟨hc, (Normalization.lessRawCode_exact q _ c).mpr
      ⟨hu.1, (Bool.and_eq_true.mp hc).1,
        by simpa only [LogEndZero.unitCode_value q] using hlt⟩⟩

open Hereditary.FinePredecessor (stripLast stripLast_primrec stripLast_split)

def lastCode (xs : List Nat) : Nat := xs.reverse.head?.getD 0

theorem lastCode_primrec : Primrec lastCode :=
  Primrec.option_getD.comp (Primrec.list_head?.comp Primrec.list_reverse) (Primrec.const 0)

@[simp] theorem lastCode_singleton (c : Nat) : lastCode [c] = c := rfl

@[simp] theorem stripLast_singleton (c : Nat) : stripLast [c] = [] := rfl

theorem lastCode_mem (xs : List Nat) (hne : xs ≠ []) : lastCode xs ∈ xs := by
  cases h : xs.reverse with
  | nil =>
    have he : xs = [] := by
      have ht := congrArg List.reverse h
      simpa only [List.reverse_reverse, List.reverse_nil] using ht
    exact False.elim (hne he)
  | cons a as =>
    have ha : a ∈ xs := List.mem_reverse.mp (by rw [h]; exact List.mem_cons_self)
    simpa only [lastCode, h, List.head?_cons, Option.getD_some] using ha

theorem lastCode_append_singleton (xs : List Nat) (c : Nat) : lastCode (xs ++ [c]) = c := by
  simp only [lastCode, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.head?_cons, Option.getD_some]

def trackingCheck (q : Nat) (xs : List Nat) : Bool :=
  !xs.isEmpty && (referenceCheck q (stripLast xs) && (principalCheck q (lastCode xs) &&
    cond (stripLast xs).isEmpty (atLeastBaseCheck q (lastCode xs))
      (aboveOneCheck q (lastCode xs) &&
        coverCheck q (lastCode (stripLast xs)) (lastCode xs))))

/-- Source3.16 in the literal original-root prefix dictionary. Every
entry is below the actual original source endpoint, and the final entry
uses its actual raw LOW spelling. The ordinal covering is the real mu.
There is no evaluation, source3.8 or resemblance hypothesis. -/
noncomputable def Tracking (q : Nat) (xs : List Nat) : Prop :=
  xs ≠ [] ∧ Reference q (stripLast xs) ∧
    lowCheckCode q (lastCode xs) = true ∧
    0 < interpretation q (lastCode xs) ∧
    Ordinal.IsPrincipal (· + ·) (interpretation q (lastCode xs)) ∧
    if stripLast xs = [] then base q ≤ interpretation q (lastCode xs)
    else 1 < interpretation q (lastCode xs) ∧
      interpretation q (lastCode xs) ≤ Mu.sourceValue q (lastCode (stripLast xs))

theorem list_isEmpty_primrec : Primrec (fun xs : List Nat => xs.isEmpty) :=
  (Primrec.beq.comp Primrec.list_length (Primrec.const 0)).of_eq
    (fun xs => by cases xs <;> simp)

theorem trackingCheck_primrec : Primrec₂ trackingCheck := by
  have hp := stripLast_primrec.comp Primrec.snd
  have hl := lastCode_primrec.comp Primrec.snd
  have hpl := lastCode_primrec.comp hp
  have hcover := coverCheck_primrec.comp ((Primrec.fst.pair hpl).pair hl)
  have hfinal := (list_isEmpty_primrec.comp hp).cond
    (atLeastBaseCheck_primrec.comp Primrec.fst hl)
    (Primrec.and.comp (aboveOneCheck_primrec.comp Primrec.fst hl) hcover)
  exact (Primrec.and.comp (Primrec.not.comp (list_isEmpty_primrec.comp Primrec.snd))
    (Primrec.and.comp (referenceCheck_primrec.comp Primrec.fst hp)
      (Primrec.and.comp (principalCheck_primrec.comp Primrec.fst hl) hfinal))).to₂

theorem trackingCheck_exact (q : Nat) (xs : List Nat) :
    trackingCheck q xs = true ↔ Tracking q xs := by
  constructor
  · intro ht
    have h := Bool.and_eq_true.mp ht
    have hne : xs ≠ [] := by
      intro he
      have hb := h.1
      simp only [he, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true] at hb
    have hr := Bool.and_eq_true.mp h.2
    have hf := Bool.and_eq_true.mp hr.2
    have hp := (principalCheck_exact q _).mp hf.1
    refine ⟨hne, (referenceCheck_exact q _).mp hr.1, hp.1, hp.2.1, hp.2.2, ?_⟩
    by_cases he : stripLast xs = []
    · rw [if_pos he]
      have hc : atLeastBaseCheck q (lastCode xs) = true := by
        simpa only [he, List.isEmpty_nil, Bool.cond_true] using hf.2
      exact ((atLeastBaseCheck_exact q _).mp hc).2
    · rw [if_neg he]
      have hi : (stripLast xs).isEmpty = false := by
        cases hs : stripLast xs <;> simp_all
      have hc : aboveOneCheck q (lastCode xs) &&
          coverCheck q (lastCode (stripLast xs)) (lastCode xs) = true := by
        simpa only [hi, Bool.cond_false] using hf.2
      have hb := Bool.and_eq_true.mp hc
      exact ⟨((aboveOneCheck_exact q _).mp hb.1).2,
        ((coverCheck_exact q _ _).mp hb.2).2.2⟩
  · rintro ⟨hne, hr, hl, hp, hprincipal, hbound⟩
    have hi : xs.isEmpty = false := by cases hs : xs <;> simp_all
    apply Bool.and_eq_true.mpr
    refine ⟨by rw [hi]; rfl, Bool.and_eq_true.mpr
      ⟨(referenceCheck_exact q _).mpr hr, Bool.and_eq_true.mpr
        ⟨(principalCheck_exact q _).mpr ⟨hl, hp, hprincipal⟩, ?_⟩⟩⟩
    by_cases he : stripLast xs = []
    · have hb : base q ≤ interpretation q (lastCode xs) := by
        simpa only [if_pos he] using hbound
      simpa only [he, List.isEmpty_nil, Bool.cond_true] using
        (atLeastBaseCheck_exact q _).mpr ⟨hl, hb⟩
    · have hempty : (stripLast xs).isEmpty = false := by
        cases hs : stripLast xs <;> simp_all
      have hb : 1 < interpretation q (lastCode xs) ∧
          interpretation q (lastCode xs) ≤ Mu.sourceValue q (lastCode (stripLast xs)) := by
        simpa only [if_neg he] using hbound
      have hroot := hr.nodes _ (lastCode_mem (stripLast xs) he)
      simpa only [hempty, Bool.cond_false] using Bool.and_eq_true.mpr
        ⟨(aboveOneCheck_exact q _).mpr ⟨hl, hb.1⟩,
          (coverCheck_exact q _ _).mpr ⟨hroot, hl, hb.2⟩⟩

/-- Erasing the final tracking entry gives an actual reference sequence.
This is the forward direction of the printed Definition3.17. -/
theorem tracking_erasure (q : Nat) (xs : List Nat) (h : trackingCheck q xs = true) :
    referenceCheck q (stripLast xs) = true :=
  (referenceCheck_exact q _).mpr ((trackingCheck_exact q xs).mp h).2.1

theorem stripLast_append_singleton (xs : List Nat) (c : Nat) : stripLast (xs ++ [c]) = xs := by
  simp only [stripLast, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.tail_cons, List.reverse_reverse]

/-- The empty reference sequence has a genuine one-entry tracking
extension at the real admitted epsilon base. -/
theorem empty_reference_extension (q : Nat) (hq : baseCheck q = true) :
    Tracking q [SourceLocalization.baseRaw q] := by
  have hn := SourceLocalization.baseRaw_node q hq
  have hv : interpretation q (SourceLocalization.baseRaw q) = base q :=
    SourceLocalization.baseRaw_value q hq
  refine ⟨by simp, Reference.nil,
    ?_, ?_, ?_, ?_⟩
  · simpa only [lastCode_singleton] using SourceLocalization.node_low q _ hn
  · simpa only [lastCode_singleton, hv] using base_pos q hq
  · have he := SourceChi.epsilon_base q hq
    have hp : Ordinal.IsPrincipal (· + ·) (base q) := by
      rw [← he]
      exact Ordinal.isPrincipal_add_omega0_opow _
    simpa only [lastCode_singleton, hv] using hp
  · simp only [stripLast_singleton, if_pos rfl, lastCode_singleton, hv, le_refl]

/-- Every nonempty genuine reference prefix has a real tracking extension:
the actual original omega code is principal and below its computed mu.
No mu covering witness is supplied. -/
theorem nonempty_reference_extension (q : Nat) (xs : List Nat)
    (h : Reference q xs) (hne : xs ≠ []) :
    Tracking q (xs ++ [OmegaPowers.powerCode q (OmegaPowerHeight.numeralCode 1)]) := by
  let root := lastCode xs
  have ha : Mu.inputCheck q root = true := h.nodes _ (lastCode_mem xs hne)
  have hq := RootLowCollapse.source_checked q root ha
  have hu := OmegaPowerHeight.numeralCode_spec q 1 hq
  have hs := OmegaPowers.powerCode_spec q (OmegaPowerHeight.numeralCode 1) hu.1
  have hv : interpretation q (OmegaPowers.powerCode q (OmegaPowerHeight.numeralCode 1)) =
      Ordinal.omega0 := by
    rw [hs.2.2, hu.2.2.1, Nat.cast_one, Ordinal.opow_one]
  have hp : Ordinal.IsPrincipal (· + ·) Ordinal.omega0 := by
    simpa only [Ordinal.opow_one] using Ordinal.isPrincipal_add_omega0_opow (1 : Ordinal.{0})
  refine ⟨by simp, by simpa only [stripLast_append_singleton] using h,
    ?_, ?_, ?_, ?_⟩
  · simpa only [lastCode_append_singleton] using hs.1
  · simpa only [lastCode_append_singleton, hv] using
      (zero_lt_one.trans Ordinal.one_lt_omega0 : 0 < Ordinal.omega0)
  · simpa only [lastCode_append_singleton, hv] using hp
  · rw [stripLast_append_singleton, if_neg hne, lastCode_append_singleton]
    refine ⟨by rw [hv]; exact Ordinal.one_lt_omega0, ?_⟩
    rw [hv]
    exact omega_le_mu q root ha

/-- Exact printed erasure characterization3.17 on the original source
dictionary. Both directions are constructed, including the empty prefix;
the actual omega extension derives its covering from the original root. -/
theorem reference_erasure_iff (q : Nat) (hq : baseCheck q = true) (xs : List Nat) :
    referenceCheck q xs = true ↔
      ∃ ys, trackingCheck q ys = true ∧ stripLast ys = xs := by
  constructor
  · intro h
    have hr := (referenceCheck_exact q xs).mp h
    by_cases he : xs = []
    · subst xs
      exact ⟨[SourceLocalization.baseRaw q],
        (trackingCheck_exact q _).mpr (empty_reference_extension q hq), rfl⟩
    · exact ⟨xs ++ [OmegaPowers.powerCode q (OmegaPowerHeight.numeralCode 1)],
        (trackingCheck_exact q _).mpr (nonempty_reference_extension q xs hr he),
        stripLast_append_singleton _ _⟩
  · rintro ⟨ys, hy, he⟩
    simpa only [he] using tracking_erasure q ys hy

theorem Tracking.baseCheck {q : Nat} {xs : List Nat} (h : Tracking q xs) :
    baseCheck q = true := (HeightBoundary.input_spec q _ h.2.2.1).2.1

/-- Every actual tracking entry lies below the original source endpoint,
including the final raw principal and every written epsilon prefix. -/
theorem Tracking.source_domain {q : Nat} {xs : List Nat} (h : Tracking q xs) :
    ∀ c ∈ xs, lowCheckCode q c = true ∧ interpretation q c < globalBoundary (base q) 0 := by
  obtain ⟨a, he, hh⟩ := stripLast_split xs h.1
  have hlast : lastCode xs = a := by simp only [lastCode, hh, Option.getD_some]
  have hs : xs = stripLast xs ++ [lastCode xs] := by simpa only [hlast] using he
  intro c hc
  rw [hs] at hc
  rcases List.mem_append.mp hc with hc | hc
  · have hn := h.2.1.nodes c hc
    exact ⟨RootLowCollapse.root_low q c hn,
      checked_low_bound q c (RootLowCollapse.root_low q c hn)⟩
  · have heq : c = lastCode xs := List.mem_singleton.mp hc
    subst c
    exact ⟨h.2.2.1, checked_low_bound q _ h.2.2.1⟩

theorem Tracking.prefix_strict {q : Nat} {xs : List Nat} (h : Tracking q xs) :
    ((stripLast xs).map (interpretation q)).Pairwise (· < ·) := h.2.1.strict

theorem Tracking.prefix_epsilons {q : Nat} {xs : List Nat} (h : Tracking q xs) :
    ∀ c ∈ stripLast xs, base q < interpretation q c ∧
      Ordinal.omega0 ^ interpretation q c = interpretation q c := by
  intro c hc
  exact ⟨(h.2.1.epsilons c hc).1, (h.2.1.epsilons c hc).2.1⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceTrackingSequences
