import Alexander313.HereditaryMasks

/-!
# Whole formula support and a concrete global stratifier

Support includes indexed atoms underneath live and ghost heads, Boolean
contexts and quantifiers. The natural-number rank stratifier constructs a
globally admissible lift of every source formula. It supplies structural
nesting only; Wilken guard room and an extension of prescribed ordinal labels
are separate constructions, not consequences of this elementary lift.
-/

namespace Alexander313

namespace Shape

variable {Owner : Type}

def rank : Shape Owner → Nat
  | .falsum => 1
  | .equal => 1
  | .imp φ ψ => φ.rank + ψ.rank + 1
  | .conj φ ψ => φ.rank + ψ.rank + 1
  | .disj φ ψ => φ.rank + ψ.rank + 1
  | .neg φ => φ.rank + 1
  | .all φ => φ.rank + 1
  | .ex φ => φ.rank + 1
  | .know _ φ => φ.rank + 1

end Shape

namespace Formula

variable {Owner Label : Type} [DecidableEq Label]

def labelSupport : Formula (RecordedHead Owner Label) → Finset Label
  | .falsum => ∅
  | .equal _ _ => ∅
  | .imp φ ψ => φ.labelSupport ∪ ψ.labelSupport
  | .conj φ ψ => φ.labelSupport ∪ ψ.labelSupport
  | .disj φ ψ => φ.labelSupport ∪ ψ.labelSupport
  | .neg φ => φ.labelSupport
  | .all _ φ => φ.labelSupport
  | .ex _ φ => φ.labelSupport
  | .know (.live _) φ => φ.labelSupport
  | .know (.indexed _ ν) φ => insert ν φ.labelSupport
  | .know (.ghost _) φ => φ.labelSupport

@[simp] theorem labelSupport_subst (φ : Formula (RecordedHead Owner Label))
    (σ : NumericalSubstitution) : (φ.subst σ).labelSupport = φ.labelSupport := by
  induction φ generalizing σ with
  | falsum => rfl
  | equal t u => rfl
  | imp φ ψ ihφ ihψ => simp only [subst, labelSupport, ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp only [subst, labelSupport, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [subst, labelSupport, ihφ, ihψ]
  | neg φ ih => exact ih σ
  | all x φ ih => exact ih (σ.remove x)
  | ex x φ ih => exact ih (σ.remove x)
  | know a φ ih => cases a <;> simp only [subst, labelSupport, ih]

@[simp] theorem labelSupport_close (φ : Formula (RecordedHead Owner Label))
    (s : Assignment) : (φ.close s).labelSupport = φ.labelSupport :=
  labelSupport_subst φ _

def GloballyStratified [LT Label] : Formula (RecordedHead Owner Label) → Prop
  | .falsum => True
  | .equal _ _ => True
  | .imp φ ψ => φ.GloballyStratified ∧ ψ.GloballyStratified
  | .conj φ ψ => φ.GloballyStratified ∧ ψ.GloballyStratified
  | .disj φ ψ => φ.GloballyStratified ∧ ψ.GloballyStratified
  | .neg φ => φ.GloballyStratified
  | .all _ φ => φ.GloballyStratified
  | .ex _ φ => φ.GloballyStratified
  | .know (.live _) φ => φ.GloballyStratified
  | .know (.indexed _ ν) φ =>
    φ.GloballyStratified ∧ ∀ μ ∈ φ.labelSupport, μ < ν
  | .know (.ghost _) φ => φ.GloballyStratified

@[simp] theorem globallyStratified_subst [LT Label]
    (φ : Formula (RecordedHead Owner Label)) (σ : NumericalSubstitution) :
    (φ.subst σ).GloballyStratified ↔ φ.GloballyStratified := by
  induction φ generalizing σ with
  | falsum => rfl
  | equal t u => rfl
  | imp φ ψ ihφ ihψ => simp only [subst, GloballyStratified, ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp only [subst, GloballyStratified, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [subst, GloballyStratified, ihφ, ihψ]
  | neg φ ih => exact ih σ
  | all x φ ih => exact ih (σ.remove x)
  | ex x φ ih => exact ih (σ.remove x)
  | know a φ ih => cases a <;>
      simp only [subst, GloballyStratified, labelSupport_subst, ih]

@[simp] theorem globallyStratified_close [LT Label]
    (φ : Formula (RecordedHead Owner Label)) (s : Assignment) :
    (φ.close s).GloballyStratified ↔ φ.GloballyStratified :=
  globallyStratified_subst φ _

end Formula

def rankHeads {Owner : Type} [DecidableEq Owner] (A : Finset Owner)
    (a : Owner) (sh : Shape Owner) : RecordedHead Owner Nat :=
  if a ∈ A then .indexed a sh.rank else .live a

theorem rankHeads_erase {Owner : Type} [DecidableEq Owner]
    (A : Finset Owner) (a : Owner) (sh : Shape Owner) :
    (rankHeads A a sh).erase = a := by
  by_cases ha : a ∈ A <;> simp [rankHeads, ha, RecordedHead.erase]

theorem rank_record_support_lt {Owner : Type} [DecidableEq Owner]
    (A : Finset Owner) (φ : Formula Owner) :
    ∀ n ∈ (φ.record (rankHeads A)).labelSupport, n < φ.shape.rank := by
  induction φ with
  | falsum => simp [Formula.record, Formula.labelSupport]
  | equal t u => simp [Formula.record, Formula.labelSupport]
  | imp φ ψ ihφ ihψ =>
    intro n hn
    rcases Finset.mem_union.mp hn with hφ | hψ
    · have h := ihφ n hφ
      change n < φ.shape.rank + ψ.shape.rank + 1
      omega
    · have h := ihψ n hψ
      change n < φ.shape.rank + ψ.shape.rank + 1
      omega
  | conj φ ψ ihφ ihψ =>
    intro n hn
    rcases Finset.mem_union.mp hn with hφ | hψ
    · have h := ihφ n hφ
      change n < φ.shape.rank + ψ.shape.rank + 1
      omega
    · have h := ihψ n hψ
      change n < φ.shape.rank + ψ.shape.rank + 1
      omega
  | disj φ ψ ihφ ihψ =>
    intro n hn
    rcases Finset.mem_union.mp hn with hφ | hψ
    · have h := ihφ n hφ
      change n < φ.shape.rank + ψ.shape.rank + 1
      omega
    · have h := ihψ n hψ
      change n < φ.shape.rank + ψ.shape.rank + 1
      omega
  | neg φ ih =>
    intro n hn
    have h := ih n hn
    change n < φ.shape.rank + 1
    omega
  | all x φ ih =>
    intro n hn
    have h := ih n hn
    change n < φ.shape.rank + 1
    omega
  | ex x φ ih =>
    intro n hn
    have h := ih n hn
    change n < φ.shape.rank + 1
    omega
  | know a φ ih =>
    intro n hn
    change n < φ.shape.rank + 1
    by_cases ha : a ∈ A
    · simp only [Formula.record, rankHeads, ha, ↓reduceIte,
        Formula.labelSupport, Finset.mem_insert] at hn
      rcases hn with rfl | hn
      · exact Nat.lt_succ_self _
      · have h := ih n hn
        omega
    · simp only [Formula.record, rankHeads, ha, ↓reduceIte,
        Formula.labelSupport] at hn
      have h := ih n hn
      omega

theorem rank_record_globally_stratified {Owner : Type} [DecidableEq Owner]
    (A : Finset Owner) (φ : Formula Owner) :
    (φ.record (rankHeads A)).GloballyStratified := by
  induction φ with
  | falsum => trivial
  | equal t u => trivial
  | imp φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | conj φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | disj φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | neg φ ih => exact ih
  | all x φ ih => exact ih
  | ex x φ ih => exact ih
  | know a φ ih =>
    by_cases ha : a ∈ A
    · simp only [Formula.record, rankHeads, ha, ↓reduceIte, Formula.GloballyStratified]
      exact ⟨ih, rank_record_support_lt A φ⟩
    · simpa only [Formula.record, rankHeads, ha, ↓reduceIte,
        Formula.GloballyStratified] using ih

end Alexander313
