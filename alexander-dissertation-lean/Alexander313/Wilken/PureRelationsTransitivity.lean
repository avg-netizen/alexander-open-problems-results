import Alexander313.Wilken.PureRelationsSemantics
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Actual transitivity, interval closure and right-limit continuity

The constructed relations use strict-upper prefixes in their defining
recursion. Every bounded tuple sees precisely the actual full relations,
so their literal prenex elementarity equations agree with the uncut pure
structure. This derives transitivity and the first relation's interval and
right-limit closure without a relation, elementarity or continuity oracle.
The second relation's interval conclusion retains the genuine first-relation
link from the intermediate endpoint to the upper endpoint. Uncompiled.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations

theorem tupleBelow_mono {n : Nat} {α β : Ordinal.{0}} (hαβ : α ≤ β)
    {v : Fin n → Ordinal.{0}} (hv : TupleBelow α v) : TupleBelow β v :=
  fun i => (hv i).trans_le hαβ

theorem tupleBelow_append {m n : Nat} (α : Ordinal.{0})
    (u : Fin m → Ordinal.{0}) (v : Fin n → Ordinal.{0})
    (hu : TupleBelow α u) (hv : TupleBelow α v) : TupleBelow α (Fin.append u v) := by
  apply (Fin.forall_fin_add (fun i => Fin.append u v i < α)).mpr
  constructor
  · intro i
    simpa only [Fin.append_left] using hu i
  · intro i
    simpa only [Fin.append_right] using hv i

/-- All atoms, including negative occurrences in a matrix, see the genuine
recursive relations whenever their tuple entries lie below the prefix. -/
theorem matrix_realize_prefix {n : Nat} (β : Ordinal.{0}) (φ : Matrix n)
    (v : Fin n → Ordinal.{0}) (hv : TupleBelow β v) :
    φ.realize (prefixFirst β) (prefixSecond β) v ↔ φ.realize R1 R2 v := by
  induction φ with
  | falsum => rfl
  | equal i j => rfl
  | lessEqual i j => rfl
  | first i j => exact prefixFirst_below (hv j)
  | second i j => exact prefixSecond_below (hv j)
  | neg φ ih => exact not_congr ih
  | conj φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | disj φ ψ ihφ ihψ => exact or_congr ihφ ihψ

theorem sigma1Truth_prefix_iff (β α : Ordinal.{0}) (hαβ : α ≤ β)
    (p m : Nat) (φ : Matrix (p + m)) (v : Fin p → Ordinal.{0})
    (hv : TupleBelow α v) :
    sigma1Truth (prefixFirst β) (prefixSecond β) α p m φ v ↔
      sigma1Truth R1 R2 α p m φ v := by
  constructor
  · rintro ⟨w, hw, hφ⟩
    exact ⟨w, hw, (matrix_realize_prefix β φ (Fin.append v w)
      (tupleBelow_mono hαβ (tupleBelow_append α v w hv hw))).mp hφ⟩
  · rintro ⟨w, hw, hφ⟩
    exact ⟨w, hw, (matrix_realize_prefix β φ (Fin.append v w)
      (tupleBelow_mono hαβ (tupleBelow_append α v w hv hw))).mpr hφ⟩

theorem sigma2Truth_prefix_iff (β α : Ordinal.{0}) (hαβ : α ≤ β)
    (p m n : Nat) (φ : Matrix ((p + m) + n)) (v : Fin p → Ordinal.{0})
    (hv : TupleBelow α v) :
    sigma2Truth (prefixFirst β) (prefixSecond β) α p m n φ v ↔
      sigma2Truth R1 R2 α p m n φ v := by
  constructor
  · rintro ⟨w, hw, hφ⟩
    refine ⟨w, hw, ?_⟩
    intro z hz
    exact (matrix_realize_prefix β φ (Fin.append (Fin.append v w) z)
      (tupleBelow_mono hαβ (tupleBelow_append α (Fin.append v w) z
        (tupleBelow_append α v w hv hw) hz))).mp (hφ z hz)
  · rintro ⟨w, hw, hφ⟩
    refine ⟨w, hw, ?_⟩
    intro z hz
    exact (matrix_realize_prefix β φ (Fin.append (Fin.append v w) z)
      (tupleBelow_mono hαβ (tupleBelow_append α (Fin.append v w) z
        (tupleBelow_append α v w hv hw) hz))).mpr (hφ z hz)

/-- The actual constructed first relation has the literal uncut pure
Sigma1 equation. Prefix agreement is proved, not assumed. -/
theorem R1_actual_iff (α β : Ordinal.{0}) : R1 α β ↔
    α ≤ β ∧ Sigma1Elementary R1 R2 α β := by
  constructor
  · intro h
    obtain ⟨hαβ, he⟩ := (R1_iff α β).mp h
    refine ⟨hαβ, ?_⟩
    intro p m φ v hv
    exact (sigma1Truth_prefix_iff β α hαβ p m φ v hv).symm.trans
      ((he p m φ v hv).trans (sigma1Truth_prefix_iff β β le_rfl p m φ v
        (tupleBelow_mono hαβ hv)))
  · rintro ⟨hαβ, he⟩
    apply (R1_iff α β).mpr
    refine ⟨hαβ, ?_⟩
    intro p m φ v hv
    exact (sigma1Truth_prefix_iff β α hαβ p m φ v hv).trans
      ((he p m φ v hv).trans (sigma1Truth_prefix_iff β β le_rfl p m φ v
        (tupleBelow_mono hαβ hv)).symm)

theorem R2_actual_iff (α β : Ordinal.{0}) : R2 α β ↔
    α ≤ β ∧ Sigma2Elementary R1 R2 α β := by
  constructor
  · intro h
    obtain ⟨hαβ, he⟩ := (R2_iff α β).mp h
    refine ⟨hαβ, ?_⟩
    intro p m n φ v hv
    exact (sigma2Truth_prefix_iff β α hαβ p m n φ v hv).symm.trans
      ((he p m n φ v hv).trans (sigma2Truth_prefix_iff β β le_rfl p m n φ v
        (tupleBelow_mono hαβ hv)))
  · rintro ⟨hαβ, he⟩
    apply (R2_iff α β).mpr
    refine ⟨hαβ, ?_⟩
    intro p m n φ v hv
    exact (sigma2Truth_prefix_iff β α hαβ p m n φ v hv).trans
      ((he p m n φ v hv).trans (sigma2Truth_prefix_iff β β le_rfl p m n φ v
        (tupleBelow_mono hαβ hv)).symm)

theorem sigma1Elementary_trans (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (α β γ : Ordinal.{0}) (hαβ : α ≤ β)
    (hab : Sigma1Elementary R₁ R₂ α β) (hbc : Sigma1Elementary R₁ R₂ β γ) :
    Sigma1Elementary R₁ R₂ α γ := by
  intro p m φ v hv
  exact (hab p m φ v hv).trans (hbc p m φ v (tupleBelow_mono hαβ hv))

theorem sigma2Elementary_trans (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (α β γ : Ordinal.{0}) (hαβ : α ≤ β)
    (hab : Sigma2Elementary R₁ R₂ α β) (hbc : Sigma2Elementary R₁ R₂ β γ) :
    Sigma2Elementary R₁ R₂ α γ := by
  intro p m n φ v hv
  exact (hab p m n φ v hv).trans (hbc p m n φ v (tupleBelow_mono hαβ hv))

theorem R1_trans {α β γ : Ordinal.{0}} (hab : R1 α β) (hbc : R1 β γ) : R1 α γ := by
  obtain ⟨hαβ, heab⟩ := (R1_actual_iff α β).mp hab
  obtain ⟨hβγ, hebc⟩ := (R1_actual_iff β γ).mp hbc
  exact (R1_actual_iff α γ).mpr ⟨hαβ.trans hβγ,
    sigma1Elementary_trans R1 R2 α β γ hαβ heab hebc⟩

theorem R2_trans {α β γ : Ordinal.{0}} (hab : R2 α β) (hbc : R2 β γ) : R2 α γ := by
  obtain ⟨hαβ, heab⟩ := (R2_actual_iff α β).mp hab
  obtain ⟨hβγ, hebc⟩ := (R2_actual_iff β γ).mp hbc
  exact (R2_actual_iff α γ).mpr ⟨hαβ.trans hβγ,
    sigma2Elementary_trans R1 R2 α β γ hαβ heab hebc⟩

theorem sigma1Truth_mono (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    {α β : Ordinal.{0}} (hαβ : α ≤ β) (p m : Nat)
    (φ : Matrix (p + m)) (v : Fin p → Ordinal.{0}) :
    sigma1Truth R₁ R₂ α p m φ v → sigma1Truth R₁ R₂ β p m φ v := by
  rintro ⟨w, hw, hφ⟩
  exact ⟨w, tupleBelow_mono hαβ hw, hφ⟩

/-- The actual first relation connects its lower endpoint to every
intermediate upper endpoint. No intervening relation is a premise. -/
theorem R1_between {α β γ : Ordinal.{0}} (hab : R1 α β)
    (hαγ : α ≤ γ) (hγβ : γ ≤ β) : R1 α γ := by
  have he := ((R1_actual_iff α β).mp hab).2
  apply (R1_actual_iff α γ).mpr
  refine ⟨hαγ, ?_⟩
  intro p m φ v hv
  constructor
  · exact sigma1Truth_mono R1 R2 hαγ p m φ v
  · intro hg
    exact (he p m φ v hv).mpr (sigma1Truth_mono R1 R2 hγβ p m φ v hg)

/-- Universal matrix truth extends from a Sigma1 elementary lower segment:
an alleged new counterexample would reflect by the genuine Sigma1 equation. -/
theorem sigma2Truth_mono_of_sigma1 (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (α β : Ordinal.{0}) (hαβ : α ≤ β) (he : Sigma1Elementary R₁ R₂ α β)
    (p m n : Nat) (φ : Matrix ((p + m) + n)) (v : Fin p → Ordinal.{0})
    (hv : TupleBelow α v) :
    sigma2Truth R₁ R₂ α p m n φ v → sigma2Truth R₁ R₂ β p m n φ v := by
  classical
  rintro ⟨w, hw, hφ⟩
  refine ⟨w, tupleBelow_mono hαβ hw, ?_⟩
  intro z hz
  by_contra hbad
  have hb : sigma1Truth R₁ R₂ β (p + m) n (.neg φ) (Fin.append v w) :=
    ⟨z, hz, hbad⟩
  obtain ⟨z', hz', hbad'⟩ := (he (p + m) n (.neg φ) (Fin.append v w)
    (tupleBelow_append α v w hv hw)).mpr hb
  exact hbad' (hφ z' hz')

/-- The second relation's connectedness uses the actual first relation
from the intermediate segment to the original upper segment. -/
theorem R2_connected {α β γ : Ordinal.{0}} (hac : R2 α γ)
    (hbc : R1 β γ) (hαβ : α ≤ β) : R2 α β := by
  have hβγ := R1_le hbc
  have hab := R1_between (R2_R1 hac) hαβ hβγ
  have heab := ((R1_actual_iff α β).mp hab).2
  have hebc := ((R1_actual_iff β γ).mp hbc).2
  have heac := ((R2_actual_iff α γ).mp hac).2
  apply (R2_actual_iff α β).mpr
  refine ⟨hαβ, ?_⟩
  intro p m n φ v hv
  constructor
  · exact sigma2Truth_mono_of_sigma1 R1 R2 α β hαβ heab p m n φ v hv
  · intro hb
    exact (heac p m n φ v hv).mpr
      (sigma2Truth_mono_of_sigma1 R1 R2 β γ hβγ hebc p m n φ v
        (tupleBelow_mono hαβ hv) hb)

/-- Every actual finite tuple below a proper limit fits strictly below
one smaller ordinal, including the empty tuple. -/
theorem tupleBelow_limit_bounded (β : Ordinal.{0}) (hβ : Order.IsSuccLimit β)
    {n : Nat} (v : Fin n → Ordinal.{0}) (hv : TupleBelow β v) :
    ∃ γ : Ordinal.{0}, γ < β ∧ TupleBelow γ v := by
  induction n with
  | zero => exact ⟨0, hβ.pos, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨γ, hγ, hw⟩ := ih (fun i => v i.succ) (fun i => hv i.succ)
    refine ⟨max γ (v 0 + 1), max_lt hγ (hβ.add_one_lt (hv 0)), ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (lt_add_one (v 0)).trans_le (le_max_right γ (v 0 + 1))
    · exact (hw j).trans_le (le_max_left γ (v 0 + 1))

/-- Genuine right-limit continuity of the constructed first relation.
Each upper existential witness lies in a smaller intermediate segment;
the already constructed relation there reflects it into the lower segment. -/
theorem R1_limit {α β : Ordinal.{0}} (hβ : Order.IsSuccLimit β) (hαβ : α < β)
    (hintermediate : ∀ γ : Ordinal.{0}, α ≤ γ → γ < β → R1 α γ) : R1 α β := by
  apply (R1_actual_iff α β).mpr
  refine ⟨hαβ.le, ?_⟩
  intro p m φ v hv
  constructor
  · exact sigma1Truth_mono R1 R2 hαβ.le p m φ v
  · rintro ⟨w, hw, hφ⟩
    obtain ⟨γ, hγβ, hwγ⟩ := tupleBelow_limit_bounded β hβ w hw
    have hδβ : max α γ < β := max_lt hαβ hγβ
    have he := ((R1_actual_iff α (max α γ)).mp
      (hintermediate (max α γ) (le_max_left α γ) hδβ)).2
    exact (he p m φ v hv).mpr
      ⟨w, tupleBelow_mono (le_max_right α γ) hwγ, hφ⟩

end Alexander313.Wilken.PureRelations
