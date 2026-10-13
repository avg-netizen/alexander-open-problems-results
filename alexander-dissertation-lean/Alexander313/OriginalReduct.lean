import Alexander313.Effective.OwnerMap
import Alexander313.SourceModels

/-!
# An actual effective original-language reduct

The fresh common operator can be represented by owner 0 and the original
owners by successors. Pulling the full sentence-theorem predicates back
along successor constructs a uniformly r.e., sentence/consequence-closed
MachineFamily. Its semantic agreement is proved at all assignments, not
assumed, and no arithmetic numeral or source compiler is recomputed.
-/

namespace Alexander313

noncomputable def EffectiveFamily.ownerMapped (F : EffectiveFamily Nat)
    (howners : ∀ i, F.encodeOwner i = i) (f : Nat → Nat) (hf : Primrec f) :
    EffectiveFamily Nat := by
  let G := Classical.choose (F.ownerMapped_exists howners f hf)
  have hG := Classical.choose_spec (F.ownerMapped_exists howners f hf)
  exact { G with
    proves := F.proves.pullback f
    recognizes_correct := fun i φ => (G.recognizes_correct i φ).trans (hG.2 i φ) }

@[simp] theorem EffectiveFamily.ownerMapped_proves (F : EffectiveFamily Nat)
    (howners : ∀ i, F.encodeOwner i = i) (f : Nat → Nat) (hf : Primrec f)
    (i : Nat) (φ : Formula Nat) :
    (F.ownerMapped howners f hf).proves i φ ↔ F.proves (f i) (φ.mapOwner f) := Iff.rfl

theorem EffectiveFamily.ownerMapped_canonical (F : EffectiveFamily Nat)
    (howners : ∀ i, F.encodeOwner i = i) (f : Nat → Nat) (hf : Primrec f) (i : Nat) :
    (F.ownerMapped howners f hf).encodeOwner i = i :=
  (Classical.choose_spec (F.ownerMapped_exists howners f hf)).1 i

noncomputable def MachineFamily.ownerMapped (F : MachineFamily)
    (f : Nat → Nat) (hf : Primrec f) : MachineFamily where
  effective := F.effective.ownerMapped F.canonical_owners f hf
  canonical_owners := F.effective.ownerMapped_canonical F.canonical_owners f hf
  sentences := by
    intro i φ hφ
    have hc := F.sentences (f i) (φ.mapOwner f) hφ
    simpa only [Formula.Closed, Formula.freeVars_mapOwner] using hc
  theory_closed := by
    intro i φ hc
    constructor
    · intro hp
      apply (F.theory_closed (f i) (φ.mapOwner f)
        (by simpa only [Formula.Closed, Formula.freeVars_mapOwner] using hc)).mp
      exact hp.mapOwner f (fun θ hθ => hθ)
    · intro hp
      exact Provable.of_axiom hp

@[simp] theorem MachineFamily.ownerMapped_proves (F : MachineFamily)
    (f : Nat → Nat) (hf : Primrec f) (i : Nat) (φ : Formula Nat) :
    (F.ownerMapped f hf).effective.proves i φ ↔
      F.effective.proves (f i) (φ.mapOwner f) := Iff.rfl

theorem MachineFamily.truth_ownerMapped (F : MachineFamily)
    (f : Nat → Nat) (hf : Primrec f) (filtered : Bool) (φ : Formula Nat) (s : Assignment) :
    truth filtered (F.ownerMapped f hf).effective.proves φ s ↔
      truth filtered F.effective.proves (φ.mapOwner f) s :=
  truth_pullback filtered F.effective.proves f φ s

theorem MachineFamily.ownerMapped_sound (F : MachineFamily)
    (f : Nat → Nat) (hf : Primrec f) (hsound : ∀ i, RawSound F.effective.proves i) :
    ∀ i, RawSound (F.ownerMapped f hf).effective.proves i := by
  intro i φ s hp
  have hsource : F.effective.proves (f i) ((φ.mapOwner f).close s) := by
    simpa only [MachineFamily.ownerMapped_proves, Formula.mapOwner_close] using hp
  exact (F.truth_ownerMapped f hf true φ s).mpr
    (hsound (f i) (φ.mapOwner f) s hsource)

/-- The designated extra owner 0 is deleted, rather than retained as an
    extra required machine in the comparator's language. -/
noncomputable def MachineFamily.originalReduct (F : MachineFamily) : MachineFamily :=
  F.ownerMapped Nat.succ Primrec.succ

@[simp] theorem MachineFamily.originalReduct_proves (F : MachineFamily)
    (i : Nat) (φ : Formula Nat) :
    F.originalReduct.effective.proves i φ ↔
      F.effective.proves (i + 1) (φ.mapOwner Nat.succ) := Iff.rfl

theorem MachineFamily.originalReduct_actualTruth (F : MachineFamily)
    (φ : Formula Nat) (s : Assignment) :
    actualTruth F.originalReduct.effective.proves φ s ↔
      actualTruth F.effective.proves (φ.mapOwner Nat.succ) s :=
  F.truth_ownerMapped Nat.succ Primrec.succ false φ s

theorem MachineFamily.originalReduct_filteredTruth (F : MachineFamily)
    (φ : Formula Nat) (s : Assignment) :
    filteredTruth F.originalReduct.effective.proves φ s ↔
      filteredTruth F.effective.proves (φ.mapOwner Nat.succ) s :=
  F.truth_ownerMapped Nat.succ Primrec.succ true φ s

end Alexander313
