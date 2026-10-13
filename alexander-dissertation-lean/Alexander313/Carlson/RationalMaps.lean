import Alexander313.Carlson.FiniteIsomorphism
import Alexander313.Carlson.AmalgamationExistence
import Mathlib.Data.List.Basic

/-! Finite rational map tables used by untrusted amalgamation certificates. -/

namespace Alexander313.Carlson

namespace Finite.RationalMap

/-- A finite list of input/output pairs. Duplicate keys use their first value. -/
abbrev Table := List (ℚ × ℚ)

/-- Evaluate the stored table, with zero as the off-table fallback. -/
def eval (t : Table) (x : ℚ) : ℚ := (t.lookup x).getD 0

/-- Record a supplied map on a finite carrier. Completeness uses this only
on the proof side; a verifier evaluates the supplied finite table itself. -/
def graph (S : Finset ℚ) (f : ℚ → ℚ) : Table :=
  (S.sort (· ≤ ·)).map (fun x => (x, f x))

@[simp] theorem eval_graph {S : Finset ℚ} {f : ℚ → ℚ} {x : ℚ} (hx : x ∈ S) :
    eval (graph S f) x = f x := by
  have h : x ∈ S.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hx
  simp only [eval, graph, List.lookup_graph f h, Option.getD_some]

@[simp] theorem eval_nil (x : ℚ) : eval [] x = 0 := rfl

@[simp] theorem eval_cons (x y z : ℚ) (t : Table) :
    eval ((x, y) :: t) z = if z = x then y else eval t z := by
  by_cases h : z = x
  · subst z
    simp [eval, List.lookup]
  · have hb : (z == x) = false := beq_eq_false_iff_ne.mpr h
    simp [eval, List.lookup, h, hb]

end Finite.RationalMap

namespace Str

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- An isomorphism depends only on the finite source carrier values. -/
theorem IsIso.congr_on_carrier {P : Str α} {Q : Str β} {f g : α → β}
    (e : IsIso P Q f) (hfix : ∀ x ∈ P.U, g x = f x) : IsIso P Q g := by
  refine ⟨(Finset.image_congr hfix).trans e.1, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [hfix x hx, hfix y hy]
    exact e.2.1 x hx y hy hxy
  · intro x hx y hy
    rw [hfix x hx, hfix y hy]
    exact e.2.2 x hx y hy

/-- Replacing the off-carrier values of every supplied embedding preserves
the original amalgamation, including its exactness and union obligations. -/
theorem Amalgamation.congr_on_carriers {n : ℕ} {P : Fin n → Str α} {Q : Str β}
    {f g : Fin n → α → β} (d : Amalgamation P Q f)
    (hfix : ∀ i, ∀ x ∈ (P i).U, g i x = f i x) : Amalgamation P Q g := by
  have himage (i : Fin n) : (P i).U.image (g i) = (P i).U.image (f i) :=
    Finset.image_congr (hfix i)
  refine ⟨d.pattern, ?_, ?_, ?_⟩
  · intro i
    rw [himage i]
    exact (d.embeddings i).congr_on_carrier (hfix i)
  · simp only [himage]
    exact d.union
  · intro i
    rw [himage i]
    exact d.exact i

end Str
end Alexander313.Carlson
