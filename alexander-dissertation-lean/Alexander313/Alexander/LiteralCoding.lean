import Alexander313.Effective.FormulaSyntax

/-!
# Primitive coding for the literal source syntax

The concrete tagged-pair serializers already have proved injectivity and
primitive-recursive exact image recognizers. Equivalence with those primitive
recursive subtypes constructs `Primcodable` instances using exactly the same
literal codes. Inverse choice is over a proved singleton code fiber; the image
and its recognition are not hypotheses of an unconstructed coding contract.
-/

namespace Alexander313

namespace Term

noncomputable def literalCodeEquiv : Term ≃ {n : Nat // isCode n = true} where
  toFun := fun t => ⟨t.code, isCode_code t⟩
  invFun := fun n => Classical.choose (isCode_sound n.val n.property)
  left_inv := fun t => code_injective
    (Classical.choose_spec (isCode_sound t.code (isCode_code t)))
  right_inv := fun n => Subtype.ext
    (Classical.choose_spec (isCode_sound n.val n.property))

noncomputable instance literalPrimcodable : Primcodable Term := by
  letI : Primcodable {n : Nat // isCode n = true} :=
    Primcodable.subtype (Primrec.eq.comp isCode_primrec (Primrec.const true))
  exact Primcodable.ofEquiv {n : Nat // isCode n = true} literalCodeEquiv

@[simp] theorem encode_eq_code (t : Term) : Encodable.encode t = t.code := rfl

theorem code_primrec : Primrec code := by
  exact (Primrec.encode : Primrec (Encodable.encode (α := Term)))

end Term

namespace Formula

noncomputable def literalCodeEquiv : Formula Nat ≃ {n : Nat // isCode n = true} where
  toFun := fun φ => ⟨φ.code id, isCode_code φ⟩
  invFun := fun n => Classical.choose (isCode_sound n.val n.property)
  left_inv := fun φ => code_injective id Function.injective_id
    (Classical.choose_spec (isCode_sound (φ.code id) (isCode_code φ)))
  right_inv := fun n => Subtype.ext
    (Classical.choose_spec (isCode_sound n.val n.property))

noncomputable instance literalPrimcodable : Primcodable (Formula Nat) := by
  letI : Primcodable {n : Nat // isCode n = true} :=
    Primcodable.subtype (Primrec.eq.comp isCode_primrec (Primrec.const true))
  exact Primcodable.ofEquiv {n : Nat // isCode n = true} literalCodeEquiv

@[simp] theorem encode_eq_code (φ : Formula Nat) : Encodable.encode φ = φ.code id := rfl

theorem code_primrec : Primrec (fun φ : Formula Nat => φ.code id) := by
  exact (Primrec.encode : Primrec (Encodable.encode (α := Formula Nat)))

end Formula

end Alexander313
