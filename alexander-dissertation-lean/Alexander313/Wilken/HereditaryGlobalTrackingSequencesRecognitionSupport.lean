import Alexander313.Wilken.HereditaryGlobalTrackingSequencesSupport
import Alexander313.Wilken.HereditaryLogEnd

/-!
# Concrete global epsilon-tail and endpoint-gap recognition

The finite fold checks all admitted canonical epsilons and their real
extended-mu covers. Its endpoint-gap comparison uses the actual zero at
segment zero and the actual finite upsilon endpoints at positive segments.
Neither an assignment nor an evaluation supplies a reference certificate.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalTrackingSequences.RecognitionSupport

open NativeContext.SourceTrackingSequences.Support (canonical_not_less_exact)

def coverCheck (a b : Nat) : Bool :=
  (GlobalMuDictionary.Support.inputCheck a && Canonical.check b) &&
    !(Canonical.less (GlobalMuDictionary.publicCode a) b)

theorem coverCheck_primrec : Primrec₂ coverCheck :=
  (Primrec.and.comp
    (Primrec.and.comp (GlobalMuDictionary.Support.inputCheck_primrec.comp Primrec.fst)
      (Canonical.Effective.check_primrec.comp Primrec.snd))
    (Primrec.not.comp (Canonical.Effective.less_primrec.comp
      (GlobalMuDictionary.publicCode_primrec.comp Primrec.fst) Primrec.snd))).to₂

theorem coverCheck_exact (a b : Nat) : coverCheck a b = true ↔
    GlobalMuDictionary.Support.inputCheck a = true ∧ Canonical.check b = true ∧
      unionInterpretation b ≤ muValue a := by
  rw [coverCheck, Bool.and_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc⟩
    have hm := GlobalMuDictionary.publicCode_spec a ha
    exact ⟨ha, hb, (canonical_not_less_exact _ _ hm.1 hb).mp hc⟩
  · rintro ⟨ha, hb, hc⟩
    have hm := GlobalMuDictionary.publicCode_spec a ha
    exact ⟨⟨ha, hb⟩, (canonical_not_less_exact _ _ hm.1 hb).mpr hc⟩

def adjacencyCheck (a b : Nat) : Bool := Canonical.less a b && coverCheck a b

theorem adjacencyCheck_primrec : Primrec₂ adjacencyCheck :=
  (Primrec.and.comp Canonical.Effective.less_primrec coverCheck_primrec).to₂

abbrev EpsilonState := Option Nat × Bool

def epsilonStep (a : Nat) (state : EpsilonState) : EpsilonState :=
  (some a, (GlobalMuDictionary.Support.inputCheck a && state.2) &&
    Option.casesOn state.1 true (fun b => adjacencyCheck a b))

theorem epsilonStep_primrec : Primrec₂ epsilonStep := by
  have hnext : Primrec₂ (fun p : Nat × EpsilonState => fun b : Nat => adjacencyCheck p.1 b) :=
    (adjacencyCheck_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  have hmore := Primrec.option_casesOn (Primrec.fst.comp Primrec.snd) (Primrec.const true) hnext
  exact ((Primrec.option_some.comp Primrec.fst).pair
    (Primrec.and.comp
      (Primrec.and.comp (GlobalMuDictionary.Support.inputCheck_primrec.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd)) hmore)).to₂

def epsilonRun (xs : List Nat) : EpsilonState := xs.foldr epsilonStep (none, true)

theorem epsilonRun_primrec : Primrec epsilonRun := by
  have hstep : Primrec₂ (fun _ : List Nat => fun p : Nat × EpsilonState => epsilonStep p.1 p.2) :=
    (Primrec.comp epsilonStep_primrec Primrec.snd).to₂
  exact Primrec.list_foldr Primrec.id (Primrec.const (none, true)) hstep

theorem epsilonRun_head (xs : List Nat) : (epsilonRun xs).1 = xs.head? := by
  cases xs <;> rfl

def epsilonCheck (xs : List Nat) : Bool := (epsilonRun xs).2

theorem epsilonCheck_primrec : Primrec epsilonCheck := Primrec.snd.comp epsilonRun_primrec

@[simp] theorem epsilonCheck_nil : epsilonCheck [] = true := rfl

theorem epsilonCheck_cons (a : Nat) (xs : List Nat) :
    epsilonCheck (a :: xs) = (GlobalMuDictionary.Support.inputCheck a && epsilonCheck xs) &&
      Option.casesOn xs.head? true (fun b => adjacencyCheck a b) := by
  change (GlobalMuDictionary.Support.inputCheck a && epsilonCheck xs) &&
    Option.casesOn (epsilonRun xs).1 true (fun b => adjacencyCheck a b) = _
  rw [epsilonRun_head]

theorem epsilonCheck_exact (xs : List Nat) : epsilonCheck xs = true ↔ EpsilonReference xs := by
  induction xs with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons a xs ih =>
    cases xs with
    | nil =>
      rw [epsilonCheck_cons]
      change (GlobalMuDictionary.Support.inputCheck a && true) && true = true ↔ EpsilonReference [a]
      simp only [Bool.and_true]
      exact ⟨fun ha => .one a ha, fun h => h.nodes a List.mem_cons_self⟩
    | cons b xs =>
      rw [epsilonCheck_cons]
      change (GlobalMuDictionary.Support.inputCheck a && epsilonCheck (b :: xs)) &&
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
          have hca := ((GlobalMuDictionary.Support.inputCheck_exact a).mp ha).1
          have hcb := ((GlobalMuDictionary.Support.inputCheck_exact b).mp hb).1
          exact ⟨⟨ha, ih.mpr ht⟩, Bool.and_eq_true.mpr
            ⟨(Canonical.less_exact a b).mpr ⟨hca, hcb, hab⟩,
              (coverCheck_exact a b).mpr ⟨ha, hcb, hcover⟩⟩⟩

/-- The actual zero segment starts at zero; endpointCode zero instead
denotes the separate E1 floor one and cannot supply this comparison. -/
def lowerEndpointCode (m : Nat) : Nat := cond (m == 0) LogEnd.zeroCode (endpointCode m)

theorem lowerEndpointCode_primrec : Primrec lowerEndpointCode :=
  (Primrec.beq.comp Primrec.id (Primrec.const 0)).cond (Primrec.const _)
    PublicEpsilonSourceDictionary.endpointCode_primrec

theorem lowerEndpointCode_spec (m : Nat) : Canonical.check (lowerEndpointCode m) = true ∧
    unionInterpretation (lowerEndpointCode m) = sourceUpsilon (m : Ordinal.{0}) := by
  cases m with
  | zero => simpa only [lowerEndpointCode, Nat.beq_refl, Bool.cond_true,
      Nat.cast_zero, sourceUpsilon_zero] using And.intro LogEnd.zeroCode_checked LogEnd.zeroCode_value
  | succ n =>
    have hz : (n + 1 == 0) = false := by simp
    simpa only [lowerEndpointCode, hz, Bool.cond_false,
      PublicUpsilonSegment.successor_value] using And.intro
      (PublicEpsilonSourceDictionary.endpointCode_checked (n + 1))
      (PublicEpsilonSourceDictionary.endpointCode_value (n + 1))

def tailGapCheck (m : Nat) (xs : List Nat) : Bool :=
  Option.casesOn xs.head? true (fun a =>
    Canonical.less (lowerEndpointCode m) a && Canonical.less a (endpointCode (m + 1)))

theorem tailGapCheck_primrec : Primrec₂ tailGapCheck := by
  have hhead := Primrec.list_head?.comp Primrec.snd
  have hm := Primrec.fst.comp Primrec.fst
  have hlow := lowerEndpointCode_primrec.comp hm
  have hupp := PublicEpsilonSourceDictionary.endpointCode_primrec.comp (Primrec.succ.comp hm)
  have htest : Primrec₂ (fun p : Nat × List Nat => fun a : Nat =>
      Canonical.less (lowerEndpointCode p.1) a && Canonical.less a (endpointCode (p.1 + 1))) :=
    (Primrec.and.comp (Canonical.Effective.less_primrec.comp hlow Primrec.snd)
      (Canonical.Effective.less_primrec.comp Primrec.snd hupp)).to₂
  exact (Primrec.option_casesOn hhead (Primrec.const true) htest).to₂

theorem tailGapCheck_exact (m : Nat) (xs : List Nat) (hr : EpsilonReference xs) :
    tailGapCheck m xs = true ↔ TailGap m xs := by
  cases xs with
  | nil => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | cons a xs =>
    have hc := ((GlobalMuDictionary.Support.inputCheck_exact a).mp (hr.nodes a List.mem_cons_self)).1
    have hl := lowerEndpointCode_spec m
    have hu := PublicEpsilonSourceDictionary.endpointCode_checked (m + 1)
    have huv : unionInterpretation (endpointCode (m + 1)) =
        sourceUpsilon ((m + 1 : Nat) : Ordinal.{0}) :=
      (PublicEpsilonSourceDictionary.endpointCode_value _).trans
        (PublicUpsilonSegment.successor_value m).symm
    change Canonical.less (lowerEndpointCode m) a && Canonical.less a (endpointCode (m + 1)) = true ↔ _
    rw [Bool.and_eq_true]
    change _ ↔ sourceUpsilon (m : Ordinal.{0}) < unionInterpretation a ∧
      unionInterpretation a < sourceUpsilon ((m + 1 : Nat) : Ordinal.{0})
    constructor
    · rintro ⟨hlo, hhi⟩
      exact ⟨by rw [← hl.2]; exact ((Canonical.less_exact _ _).mp hlo).2.2,
        by rw [← huv]; exact ((Canonical.less_exact _ _).mp hhi).2.2⟩
    · rintro ⟨hlo, hhi⟩
      exact ⟨(Canonical.less_exact _ _).mpr ⟨hl.1, hc, by rw [hl.2]; exact hlo⟩,
        (Canonical.less_exact _ _).mpr ⟨hc, hu, by
          rw [huv]; exact hhi⟩⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalTrackingSequences.RecognitionSupport
