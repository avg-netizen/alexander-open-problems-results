import Alexander313.Wilken.HereditarySkPublicTracking
import Alexander313.Wilken.HereditaryFinitePowers

/-!
# Executing finite canonical public reference and tracking recognition

All guards are concrete canonical checks, independently executing public
mu codes, and genuine canonical ordinal comparisons. The finite fold
recognizes exactly the separately defined relative reference certificate.
The final entry uses actual public principal recognition and its actual
mu cover. No tracking assignment or evaluation supplies these predicates.
Global finite-upsilon prefixes are separate. Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicTrackingSequences

open SkPublicRecurrence (muValue mu_input_canonical)
open Hereditary.FinePredecessor (stripLast stripLast_primrec)
open NativeContext.SourceTrackingSequences (lastCode lastCode_primrec lastCode_mem)
open NativeContext.SourceTrackingSequences.Support (canonical_not_less_exact)

/-- Actual checked comparison with the independently computed public mu. -/
def coverCheck (a b : Nat) : Bool :=
  (MuPublicDictionary.Support.inputCheck a && Canonical.check b) &&
    !(Canonical.less (MuPublicDictionary.publicCode a) b)

theorem coverCheck_primrec : Primrec₂ coverCheck :=
  (Primrec.and.comp
    (Primrec.and.comp (MuPublicDictionary.Support.inputCheck_primrec.comp Primrec.fst)
      (Canonical.Effective.check_primrec.comp Primrec.snd))
    (Primrec.not.comp (Canonical.Effective.less_primrec.comp
      (MuPublicDictionary.publicCode_primrec.comp Primrec.fst) Primrec.snd))).to₂

theorem coverCheck_exact (a b : Nat) : coverCheck a b = true ↔
    MuPublicDictionary.Support.inputCheck a = true ∧ Canonical.check b = true ∧
      unionInterpretation b ≤ muValue a := by
  rw [coverCheck, Bool.and_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc⟩
    have hm := MuPublicDictionary.publicCode_spec a ha
    exact ⟨ha, hb, (canonical_not_less_exact _ _ hm.1 hb).mp hc⟩
  · rintro ⟨ha, hb, hc⟩
    have hm := MuPublicDictionary.publicCode_spec a ha
    exact ⟨⟨ha, hb⟩, (canonical_not_less_exact _ _ hm.1 hb).mpr hc⟩

def adjacencyCheck (a b : Nat) : Bool := Canonical.less a b && coverCheck a b

theorem adjacencyCheck_primrec : Primrec₂ adjacencyCheck :=
  (Primrec.and.comp Canonical.Effective.less_primrec coverCheck_primrec).to₂

abbrev ReferenceState := Option Nat × Bool

def referenceStep (a : Nat) (state : ReferenceState) : ReferenceState :=
  (some a, (MuPublicDictionary.Support.inputCheck a && state.2) &&
    Option.casesOn state.1 true (fun b => adjacencyCheck a b))

theorem referenceStep_primrec : Primrec₂ referenceStep := by
  have hnext : Primrec₂ (fun p : Nat × ReferenceState => fun b : Nat => adjacencyCheck p.1 b) :=
    (adjacencyCheck_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  have hmore := Primrec.option_casesOn (Primrec.fst.comp Primrec.snd) (Primrec.const true) hnext
  exact ((Primrec.option_some.comp Primrec.fst).pair
    (Primrec.and.comp
      (Primrec.and.comp (MuPublicDictionary.Support.inputCheck_primrec.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd)) hmore)).to₂

def referenceRun (xs : List Nat) : ReferenceState :=
  xs.foldr referenceStep (none, true)

theorem referenceRun_primrec : Primrec referenceRun := by
  have hstep : Primrec₂ (fun _ : List Nat => fun s : Nat × ReferenceState => referenceStep s.1 s.2) :=
    (Primrec.comp referenceStep_primrec Primrec.snd).to₂
  exact Primrec.list_foldr Primrec.id (Primrec.const (none, true)) hstep

theorem referenceRun_head (xs : List Nat) : (referenceRun xs).1 = xs.head? := by
  cases xs <;> rfl

def referenceCheck (xs : List Nat) : Bool := (referenceRun xs).2

theorem referenceCheck_primrec : Primrec referenceCheck :=
  Primrec.snd.comp referenceRun_primrec

@[simp] theorem referenceCheck_nil : referenceCheck [] = true := rfl

theorem referenceCheck_cons (a : Nat) (xs : List Nat) :
    referenceCheck (a :: xs) = (MuPublicDictionary.Support.inputCheck a && referenceCheck xs) &&
      Option.casesOn xs.head? true (fun b => adjacencyCheck a b) := by
  change (MuPublicDictionary.Support.inputCheck a && referenceCheck xs) &&
    Option.casesOn (referenceRun xs).1 true (fun b => adjacencyCheck a b) = _
  rw [referenceRun_head]

theorem referenceCheck_exact (xs : List Nat) : referenceCheck xs = true ↔ Reference xs := by
  induction xs with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons a xs ih =>
    cases xs with
    | nil =>
      rw [referenceCheck_cons]
      change (MuPublicDictionary.Support.inputCheck a && true) && true = true ↔ Reference [a]
      simp only [Bool.and_true]
      exact ⟨fun ha => .one a ha, fun h => h.nodes a List.mem_cons_self⟩
    | cons b xs =>
      rw [referenceCheck_cons]
      change (MuPublicDictionary.Support.inputCheck a && referenceCheck (b :: xs)) &&
        adjacencyCheck a b = true ↔ _
      rw [Bool.and_eq_true, Bool.and_eq_true]
      constructor
      · rintro ⟨⟨ha, ht⟩, hadj⟩
        have hs := Bool.and_eq_true.mp hadj
        exact .cons a b xs ha ((Canonical.less_exact a b).mp hs.1).2.2
          ((coverCheck_exact a b).mp hs.2).2.2 (ih.mp ht)
      · intro h
        cases h with
        | cons a b xs ha hab hcover ht =>
          have hb := ht.nodes b List.mem_cons_self
          exact ⟨⟨ha, ih.mpr ht⟩, Bool.and_eq_true.mpr
            ⟨(Canonical.less_exact a b).mpr
              ⟨mu_input_canonical a ha, mu_input_canonical b hb, hab⟩,
              (coverCheck_exact a b).mpr ⟨ha, mu_input_canonical b hb, hcover⟩⟩⟩

def canonicalWordCheck (xs : List Nat) : Bool := xs.all Canonical.check

theorem canonicalWordCheck_primrec : Primrec canonicalWordCheck := by
  have ht : Primrec₂ (fun _ : List Nat => fun c : Nat => Canonical.check c) :=
    (Canonical.Effective.check_primrec.comp Primrec.snd).to₂
  exact (SourceOne.Comparison.Effective.listAll_primrec _ ht).comp Primrec.id Primrec.id

theorem canonicalWordCheck_exact (xs : List Nat) : canonicalWordCheck xs = true ↔
    ∀ c ∈ xs, Canonical.check c = true := List.all_eq_true

def principalCheck (c : Nat) : Bool := Canonical.check c && Principal.unionPrincipalCheck c

theorem principalCheck_primrec : Primrec principalCheck :=
  Primrec.and.comp Canonical.Effective.check_primrec Principal.unionPrincipalCheck_primrec

theorem principalCheck_exact (c : Nat) : principalCheck c = true ↔
    Canonical.check c = true ∧ 0 < unionInterpretation c ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation c) := by
  rw [principalCheck, Bool.and_eq_true, Principal.unionPrincipalCheck_exact]
  exact ⟨fun ⟨hc, _, hp, ha⟩ => ⟨hc, hp, ha⟩,
    fun ⟨hc, hp, ha⟩ => ⟨hc, Canonical.check_original hc, hp, ha⟩⟩

def atLeastOneCheck (c : Nat) : Bool :=
  Canonical.check c && !(Canonical.less c FinitePowers.oneCode)

theorem atLeastOneCheck_primrec : Primrec atLeastOneCheck :=
  Primrec.and.comp Canonical.Effective.check_primrec
    (Primrec.not.comp (Canonical.Effective.less_primrec.comp Primrec.id (Primrec.const _)))

theorem atLeastOneCheck_exact (c : Nat) : atLeastOneCheck c = true ↔
    Canonical.check c = true ∧ 1 ≤ unionInterpretation c := by
  rw [atLeastOneCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, hb⟩
    exact ⟨hc, by simpa only [FinitePowers.oneCode_value] using
      (canonical_not_less_exact _ _ hc FinitePowers.oneCode_checked).mp hb⟩
  · rintro ⟨hc, hb⟩
    exact ⟨hc, (canonical_not_less_exact _ _ hc FinitePowers.oneCode_checked).mpr
      (by simpa only [FinitePowers.oneCode_value] using hb)⟩

def aboveOneCheck (c : Nat) : Bool := Canonical.check c && Canonical.less FinitePowers.oneCode c

theorem aboveOneCheck_primrec : Primrec aboveOneCheck :=
  Primrec.and.comp Canonical.Effective.check_primrec
    (Canonical.Effective.less_primrec.comp (Primrec.const _) Primrec.id)

theorem aboveOneCheck_exact (c : Nat) : aboveOneCheck c = true ↔
    Canonical.check c = true ∧ 1 < unionInterpretation c := by
  rw [aboveOneCheck, Bool.and_eq_true]
  constructor
  · rintro ⟨hc, hb⟩
    exact ⟨hc, by simpa only [FinitePowers.oneCode_value] using ((Canonical.less_exact _ _).mp hb).2.2⟩
  · rintro ⟨hc, hb⟩
    exact ⟨hc, (Canonical.less_exact _ _).mpr ⟨FinitePowers.oneCode_checked, hc,
      by simpa only [FinitePowers.oneCode_value] using hb⟩⟩

def trackingCheck (xs : List Nat) : Bool := !xs.isEmpty &&
  (canonicalWordCheck xs && (referenceCheck (stripLast xs) && (principalCheck (lastCode xs) &&
    cond (stripLast xs).isEmpty (atLeastOneCheck (lastCode xs))
      (aboveOneCheck (lastCode xs) && coverCheck (lastCode (stripLast xs)) (lastCode xs)))))

theorem trackingCheck_primrec : Primrec trackingCheck := by
  have hp := stripLast_primrec
  have hl := lastCode_primrec
  have hpl := lastCode_primrec.comp hp
  have hcover := coverCheck_primrec.comp hpl hl
  have hfinal := (NativeContext.SourceTrackingSequences.list_isEmpty_primrec.comp hp).cond
    (atLeastOneCheck_primrec.comp hl)
    (Primrec.and.comp (aboveOneCheck_primrec.comp hl) hcover)
  exact Primrec.and.comp (Primrec.not.comp NativeContext.SourceTrackingSequences.list_isEmpty_primrec)
    (Primrec.and.comp canonicalWordCheck_primrec
      (Primrec.and.comp (referenceCheck_primrec.comp hp)
        (Primrec.and.comp (principalCheck_primrec.comp hl) hfinal)))

theorem trackingCheck_exact (xs : List Nat) : trackingCheck xs = true ↔ Tracking xs := by
  constructor
  · intro ht
    have h := Bool.and_eq_true.mp ht
    have hne : xs ≠ [] := by
      intro he
      have hb := h.1
      simp only [he, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true] at hb
    have hall := Bool.and_eq_true.mp h.2
    have hr := Bool.and_eq_true.mp hall.2
    have hf := Bool.and_eq_true.mp hr.2
    have hp := (principalCheck_exact _).mp hf.1
    refine ⟨hne, (canonicalWordCheck_exact _).mp hall.1,
      (referenceCheck_exact _).mp hr.1, hp.2.1, hp.2.2, ?_⟩
    by_cases he : stripLast xs = []
    · rw [if_pos he]
      have hc : atLeastOneCheck (lastCode xs) = true := by
        simpa only [he, List.isEmpty_nil, Bool.cond_true] using hf.2
      exact ((atLeastOneCheck_exact _).mp hc).2
    · rw [if_neg he]
      have hi : (stripLast xs).isEmpty = false := by
        cases hs : stripLast xs <;> simp_all
      have hc : aboveOneCheck (lastCode xs) && coverCheck (lastCode (stripLast xs)) (lastCode xs) = true := by
        simpa only [hi, Bool.cond_false] using hf.2
      have hb := Bool.and_eq_true.mp hc
      exact ⟨((aboveOneCheck_exact _).mp hb.1).2, ((coverCheck_exact _ _).mp hb.2).2.2⟩
  · rintro ⟨hne, hall, hr, hp, hprincipal, hbound⟩
    have hi : xs.isEmpty = false := by cases hs : xs <;> simp_all
    have hl := hall _ (lastCode_mem xs hne)
    apply Bool.and_eq_true.mpr
    refine ⟨by rw [hi]; rfl, Bool.and_eq_true.mpr
      ⟨(canonicalWordCheck_exact _).mpr hall, Bool.and_eq_true.mpr
        ⟨(referenceCheck_exact _).mpr hr, Bool.and_eq_true.mpr
          ⟨(principalCheck_exact _).mpr ⟨hl, hp, hprincipal⟩, ?_⟩⟩⟩⟩
    by_cases he : stripLast xs = []
    · have hb : 1 ≤ unionInterpretation (lastCode xs) := by simpa only [if_pos he] using hbound
      simpa only [he, List.isEmpty_nil, Bool.cond_true] using (atLeastOneCheck_exact _).mpr ⟨hl, hb⟩
    · have hempty : (stripLast xs).isEmpty = false := by
        cases hs : stripLast xs <;> simp_all
      have hb : 1 < unionInterpretation (lastCode xs) ∧
          unionInterpretation (lastCode xs) ≤ muValue (lastCode (stripLast xs)) := by
        simpa only [if_neg he] using hbound
      have hroot := hr.nodes _ (lastCode_mem (stripLast xs) he)
      simpa only [hempty, Bool.cond_false] using Bool.and_eq_true.mpr
        ⟨(aboveOneCheck_exact _).mpr ⟨hl, hb.1⟩, (coverCheck_exact _ _).mpr ⟨hroot, hl, hb.2⟩⟩

/-- Actual canonical public sk execution derives its finite numerical
tracking certificate on the printed multiplicative cutoff domain. -/
theorem execute_trackingCheck (gamma cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ SkPublicDictionary.execute (gamma, cutoff))
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hone : 1 < unionInterpretation cutoff) : trackingCheck codes = true :=
  (trackingCheck_exact _).mpr (SkPublicRecurrence.execute_tracking gamma cutoff codes ho hm hone)

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicTrackingSequences
