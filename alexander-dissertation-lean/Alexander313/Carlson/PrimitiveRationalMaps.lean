import Alexander313.Carlson.RationalMaps
import Alexander313.Carlson.PrimitiveRationalPresentation
import Mathlib.Computability.Primrec.List

/-! Primitive-recursive evaluation of the actual finite rational map tables. -/

namespace Alexander313.Carlson.PrimitiveRationalMaps

open Finite Encodable

theorem eval_eq_foldr (t : RationalMap.Table) (x : ℚ) :
    RationalMap.eval t x = t.foldr (fun xy v => if x = xy.1 then xy.2 else v) 0 := by
  induction t with
  | nil => rfl
  | cons xy t ih =>
    rw [List.foldr_cons, ← ih, RationalMap.eval_cons]

/-- Lookup uses the first stored key and its ordinary zero fallback,
including malformed maps with duplicate or omitted keys. -/
theorem eval_primrec : Primrec₂ RationalMap.eval := by
  have step : Primrec (fun p : (RationalMap.Table × ℚ) × ((ℚ × ℚ) × ℚ) =>
      if p.1.2 = p.2.1.1 then p.2.1.2 else p.2.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.fst (Primrec.const (0 : ℚ)) step.to₂).of_eq
    (fun p => (eval_eq_foldr p.1 p.2).symm)

/-- Every finite table and rational argument has a total machine answer. -/
theorem eval_program : ∃ machine : Nat.Partrec.Code,
    ∀ (t : RationalMap.Table) (x : ℚ),
      machine.eval (Nat.pair (encode t) (encode x)) =
        Part.some (encode (RationalMap.eval t x)) := by
  obtain ⟨machine, hm⟩ := PrimitiveRationalPresentation.exists_code eval_primrec
  exact ⟨machine, fun t x => hm (t, x)⟩

end Alexander313.Carlson.PrimitiveRationalMaps
