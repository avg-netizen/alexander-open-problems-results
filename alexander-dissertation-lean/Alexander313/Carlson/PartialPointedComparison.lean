import Alexander313.Carlson.PartialAmalgamationSearch
import Alexander313.Carlson.ComputablePointedComparison

/-!
# A machine for comparison in the actual pointed core

One partial-recursive machine operates on two finite presentations and their
distinguished rational points. Every typed pointed-pattern input terminates.
Its five encoded Boolean outputs are the actual equality, order, R1 and R2
answers proved for `PointedPattern.compare`.
-/

namespace Alexander313.Carlson.PartialPointedComparison

open Finite PrimitiveAmalgamationCertificates PrimitiveRationalPresentation

abbrev Input := (RationalPresentation × ℚ) × (RationalPresentation × ℚ)
abbrev Answers := Bool × Bool × Bool × Bool × Bool

def input (p q : PointedPattern) : Input := ((p.seed.val, p.point), (q.seed.val, q.point))

def family (s : Input) (i : Fin 2) : RationalPresentation := Fin.cases s.1.1 (fun _ => s.2.1) i

theorem family_primrec : Primrec family := by
  have h : Primrec₂ (fun (i : Fin 2) (s : Input) => family s i) := by
    apply Primrec.fin_curry₁.mpr
    intro i
    refine Fin.cases (Primrec.fst.comp Primrec.fst) (fun i => ?_) i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact Primrec.fst.comp Primrec.snd
  exact Primrec.fin_curry.mpr (h.comp Primrec.snd Primrec.fst)

def answers (c : PointedPattern.Comparison) : Answers := (c.eq, c.le, c.lt, c.one, c.two)

def read (s : Input) (code : ℕ) : Answers :=
  let c := (Encodable.decode (α := AmalgamationCertificate 2) code).getD
    (ComputableAmalgamation.emptyCertificate 2)
  let x := c.maps 0 s.1.2
  let y := c.maps 1 s.2.2
  (decide (x = y), decide (x ≤ y), decide (x < y),
    decide ((x, y) ∈ c.1.r₁), decide ((x, y) ∈ c.1.r₂))

theorem read_primrec : Primrec₂ read := by
  have hc : Primrec (fun s : Input × ℕ =>
      (Encodable.decode (α := AmalgamationCertificate 2) s.2).getD
        (ComputableAmalgamation.emptyCertificate 2)) :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd)
      (Primrec.const (ComputableAmalgamation.emptyCertificate 2))
  have ht := Primrec.fst.comp (Primrec.snd.comp hc)
  have hx : Primrec (fun s : Input × ℕ =>
      ((Encodable.decode (α := AmalgamationCertificate 2) s.2).getD
        (ComputableAmalgamation.emptyCertificate 2)).maps 0 s.1.1.2) :=
    PrimitiveRationalMaps.eval_primrec.comp
      (Primrec.fin_app.comp ht (Primrec.const (0 : Fin 2)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hy : Primrec (fun s : Input × ℕ =>
      ((Encodable.decode (α := AmalgamationCertificate 2) s.2).getD
        (ComputableAmalgamation.emptyCertificate 2)).maps 1 s.1.2.2) :=
    PrimitiveRationalMaps.eval_primrec.comp
      (Primrec.fin_app.comp ht (Primrec.const (1 : Fin 2)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hQ := Primrec.fst.comp hc
  exact (Primrec.eq.comp hx hy).decide.pair
    ((PrimitiveRationalData.rat_le.comp hx hy).decide.pair
      ((PrimitiveRationalData.rat_lt.comp hx hy).decide.pair
        ((relation₁_mem.comp hQ (hx.pair hy)).decide.pair
          (relation₂_mem.comp hQ (hx.pair hy)).decide)))

def compare (s : Input) : Part Answers :=
  (PartialAmalgamationSearch.search (family s)).bind (fun code => Part.some (read s code))

theorem compare_partrec : Partrec compare :=
  (PartialAmalgamationSearch.search_partrec.comp family_primrec.to_comp).bind
    read_primrec.to_comp.partrec₂

theorem compare_eq (p q : PointedPattern) :
    compare (input p q) = Part.some (answers (PointedPattern.compare p q)) := by
  have hf : family (input p q) = PointedPattern.pairFamily p q := rfl
  unfold compare
  rw [hf, PartialAmalgamationSearch.search_eq_leastCode _ (PointedPattern.pairFamily_pattern p q),
    Part.bind_some]
  rfl

/-- One machine computes all five answers on every valid pointed input;
no ordinal realization or semantic comparison oracle is an input. -/
theorem comparison_program : ∃ machine : Nat.Partrec.Code, ∀ p q : PointedPattern,
    machine.eval (Encodable.encode (input p q)) =
      Part.some (Encodable.encode (answers (PointedPattern.compare p q))) := by
  obtain ⟨machine, hm⟩ := Nat.Partrec.Code.exists_code.mp compare_partrec
  refine ⟨machine, fun p q => ?_⟩
  rw [hm]
  change (Part.bind (Part.ofOption (Encodable.decode (Encodable.encode (input p q))))
    (fun s => (compare s).map Encodable.encode)) = _
  simp only [Encodable.encodek, Part.ofOption, Part.bind_some, compare_eq, Part.map_some]

end Alexander313.Carlson.PartialPointedComparison
