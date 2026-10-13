import Alexander313.Computability

/-!
# An executing Program's order relation

The relation is the positive computation domain on the literal ordered pair.
No numerical-code comparison or order law is inserted. In particular, this
definition does not construct Wilken's actual ordinal comparison algorithm.
-/

namespace Alexander313.Program

def orderLT (order : Program) : LT Nat :=
  ⟨fun μ ν => order.domain (Nat.pair μ ν)⟩

@[simp] theorem orderLT_iff (order : Program) (μ ν : Nat) :
    @LT.lt Nat (orderLT order) μ ν ↔ order.domain (Nat.pair μ ν) := Iff.rfl

end Alexander313.Program
