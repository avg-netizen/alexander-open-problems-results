import Alexander313.Syntax

namespace Alexander313

/-- A concrete finite-tree serialization; no classical choice of a
    countable encoding is used. -/
def Term.code : Term → Nat
  | .var x => Nat.succ (Nat.pair 0 x)
  | .zero => Nat.succ (Nat.pair 1 0)
  | .succ t => Nat.succ (Nat.pair 2 t.code)
  | .add t u => Nat.succ (Nat.pair 3 (Nat.pair t.code u.code))
  | .mul t u => Nat.succ (Nat.pair 4 (Nat.pair t.code u.code))

theorem Term.code_injective : Function.Injective Term.code := by
  intro t u h
  induction t generalizing u <;> cases u <;>
    simp_all [Term.code, Nat.pair_eq_pair] <;> aesop

@[simp] theorem Term.code_eq_iff (t u : Term) : t.code = u.code ↔ t = u :=
  Term.code_injective.eq_iff

def Formula.code {Owner : Type} (ownerCode : Owner → Nat) : Formula Owner → Nat
  | .falsum => Nat.succ (Nat.pair 0 0)
  | .equal t u => Nat.succ (Nat.pair 1 (Nat.pair t.code u.code))
  | .imp φ ψ => Nat.succ (Nat.pair 2 (Nat.pair (φ.code ownerCode) (ψ.code ownerCode)))
  | .conj φ ψ => Nat.succ (Nat.pair 3 (Nat.pair (φ.code ownerCode) (ψ.code ownerCode)))
  | .disj φ ψ => Nat.succ (Nat.pair 4 (Nat.pair (φ.code ownerCode) (ψ.code ownerCode)))
  | .neg φ => Nat.succ (Nat.pair 5 (φ.code ownerCode))
  | .all x φ => Nat.succ (Nat.pair 6 (Nat.pair x (φ.code ownerCode)))
  | .ex x φ => Nat.succ (Nat.pair 7 (Nat.pair x (φ.code ownerCode)))
  | .know a φ => Nat.succ (Nat.pair 8 (Nat.pair (ownerCode a) (φ.code ownerCode)))

theorem Formula.code_injective {Owner : Type} (ownerCode : Owner → Nat)
    (howner : Function.Injective ownerCode) : Function.Injective (Formula.code ownerCode) := by
  intro φ ψ h
  induction φ generalizing ψ <;> cases ψ <;>
    simp_all [Formula.code, Nat.pair_eq_pair, howner.eq_iff] <;> aesop

end Alexander313
