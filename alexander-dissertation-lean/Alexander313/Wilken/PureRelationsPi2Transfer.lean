import Alexander313.Wilken.PureRelationsTransitivity

/-!
# Actual universal-existential transfer for the pure second relation

The displayed universal-existential sentence is the negation of one literal
existential-universal sentence with negated matrix. Actual R2 elementarity
therefore preserves it in both directions, with the ORIGINAL finite lower
parameter tuple. This supplies the quantified-transfer part of source1.7(1)
without assuming a copy, repeated-pattern or cofinal-room theorem. Literal
finite-pattern encodings and their premise truth are separate constructions.
These source candidates remain uncompiled and outside the checkpoint.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations

def pi2Truth (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop) (α : Ordinal.{0})
    (p m n : Nat) (φ : Matrix ((p + m) + n)) (v : Fin p → Ordinal.{0}) : Prop :=
  ∀ w : Fin m → Ordinal.{0}, TupleBelow α w →
    ∃ z : Fin n → Ordinal.{0}, TupleBelow α z ∧
      φ.realize R₁ R₂ (Fin.append (Fin.append v w) z)

theorem pi2Truth_iff_not_sigma2Truth_neg (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (α : Ordinal.{0}) (p m n : Nat) (φ : Matrix ((p + m) + n))
    (v : Fin p → Ordinal.{0}) :
    pi2Truth R₁ R₂ α p m n φ v ↔ ¬ sigma2Truth R₁ R₂ α p m n (.neg φ) v := by
  classical
  constructor
  · intro hpi hs
    obtain ⟨w, hw, hneg⟩ := hs
    obtain ⟨z, hz, hφ⟩ := hpi w hw
    exact hneg z hz hφ
  · intro hnot w hw
    by_contra hnone
    apply hnot
    refine ⟨w, hw, ?_⟩
    intro z hz hφ
    exact hnone ⟨z, hz, hφ⟩

theorem sigma2Elementary_pi2 (R₁ R₂ : Ordinal.{0} → Ordinal.{0} → Prop)
    (α β : Ordinal.{0}) (he : Sigma2Elementary R₁ R₂ α β)
    (p m n : Nat) (φ : Matrix ((p + m) + n)) (v : Fin p → Ordinal.{0})
    (hv : TupleBelow α v) :
    pi2Truth R₁ R₂ α p m n φ v ↔ pi2Truth R₁ R₂ β p m n φ v :=
  (pi2Truth_iff_not_sigma2Truth_neg R₁ R₂ α p m n φ v).trans
    ((not_congr (he p m n (.neg φ) v hv)).trans
      (pi2Truth_iff_not_sigma2Truth_neg R₁ R₂ β p m n φ v).symm)

/-- Actual R2 preserves the whole literal universal-existential statement
in both directions. Its elementarity is DERIVED from the constructed R2;
the only parameter guard is the original tuple lying below alpha. -/
theorem R2_pi2Truth_iff (α β : Ordinal.{0}) (hR : R2 α β)
    (p m n : Nat) (φ : Matrix ((p + m) + n)) (v : Fin p → Ordinal.{0})
    (hv : TupleBelow α v) :
    pi2Truth R1 R2 α p m n φ v ↔ pi2Truth R1 R2 β p m n φ v :=
  sigma2Elementary_pi2 R1 R2 α β ((R2_actual_iff α β).mp hR).2 p m n φ v hv

end Alexander313.Wilken.PureRelations
