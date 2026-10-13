import Alexander313.Carlson.PrimitiveFiniteData

/-!
# Primitive-recursive finite extrema with empty-set defaults

`minD s d` and `maxD s d` return the ordinary finite minimum or maximum
when `s` is nonempty, and return `d` exactly in the empty-set branch.
The supplied default does not participate in a nonempty extremum.

The certificates use the existing finite-set encoding and its canonical
list view. That list is sorted by element codes, which need not agree with
the ambient linear order. We therefore compute the ambient minimum or
maximum by a list fold. A primitive-recursive certificate for the ambient
comparison is an explicit hypothesis throughout the computability results.
-/

namespace Alexander313.Carlson.PrimitiveFiniteExtrema

open PrimitiveFiniteData

variable {α : Type*} [LinearOrder α]

/-- The minimum of a nonempty finite set, with the supplied empty-set default. -/
def minD (s : Finset α) (d : α) : α :=
  if hs : s.Nonempty then s.min' hs else d

/-- The maximum of a nonempty finite set, with the supplied empty-set default. -/
def maxD (s : Finset α) (d : α) : α :=
  if hs : s.Nonempty then s.max' hs else d

@[simp] theorem minD_empty (d : α) : minD ∅ d = d := by
  simp [minD]

@[simp] theorem maxD_empty (d : α) : maxD ∅ d = d := by
  simp [maxD]

/-- A nonempty minimum is independent of the default. -/
theorem minD_of_nonempty (s : Finset α) (d : α) (hs : s.Nonempty) :
    minD s d = s.min' hs := by
  simp [minD, hs]

/-- A nonempty maximum is independent of the default. -/
theorem maxD_of_nonempty (s : Finset α) (d : α) (hs : s.Nonempty) :
    maxD s d = s.max' hs := by
  simp [maxD, hs]

@[simp] theorem minD_singleton (a d : α) : minD {a} d = a := by
  simp [minD]

@[simp] theorem maxD_singleton (a d : α) : maxD {a} d = a := by
  simp [maxD]

/-- On a nonempty set the result is a member below every member. -/
theorem minD_spec (s : Finset α) (d : α) (hs : s.Nonempty) :
    minD s d ∈ s ∧ ∀ a ∈ s, minD s d ≤ a := by
  rw [minD_of_nonempty s d hs]
  exact ⟨s.min'_mem hs, s.min'_le⟩

/-- On a nonempty set the result is a member above every member. -/
theorem maxD_spec (s : Finset α) (d : α) (hs : s.Nonempty) :
    maxD s d ∈ s ∧ ∀ a ∈ s, a ≤ maxD s d := by
  rw [maxD_of_nonempty s d hs]
  exact ⟨s.max'_mem hs, s.le_max'⟩

theorem minD_le_of_mem (s : Finset α) (d : α) {a : α} (ha : a ∈ s) :
    minD s d ≤ a :=
  (minD_spec s d ⟨a, ha⟩).2 a ha

theorem le_maxD_of_mem (s : Finset α) (d : α) {a : α} (ha : a ∈ s) :
    a ≤ maxD s d :=
  (maxD_spec s d ⟨a, ha⟩).2 a ha

theorem minD_eq_iff (s : Finset α) (d a : α) (hs : s.Nonempty) :
    minD s d = a ↔ a ∈ s ∧ ∀ b ∈ s, a ≤ b := by
  rw [minD_of_nonempty s d hs]
  exact s.min'_eq_iff hs a

theorem maxD_eq_iff (s : Finset α) (d a : α) (hs : s.Nonempty) :
    maxD s d = a ↔ a ∈ s ∧ ∀ b ∈ s, b ≤ a := by
  rw [maxD_of_nonempty s d hs]
  exact s.max'_eq_iff hs a

section Primitive

variable [Primcodable α]

/-- The ambient binary minimum uses its certified comparison. -/
theorem min_primrec (hle : PrimrecRel (fun a b : α => a ≤ b)) :
    Primrec₂ (min : α → α → α) :=
  (Primrec.ite hle Primrec.fst Primrec.snd).of_eq fun p =>
    (min_def p.1 p.2).symm

/-- The ambient binary maximum uses its certified comparison. -/
theorem max_primrec (hle : PrimrecRel (fun a b : α => a ≤ b)) :
    Primrec₂ (max : α → α → α) :=
  (Primrec.ite hle Primrec.snd Primrec.fst).of_eq fun p =>
    (max_def p.1 p.2).symm

/-- The ordinary optional list minimum is primitive recursive. Its
nonempty branch folds from the first element, without an external default. -/
theorem list_min?_primrec (hle : PrimrecRel (fun a b : α => a ≤ b)) :
    Primrec (List.min? : List α → Option α) := by
  have hfold : Primrec (fun p : α × List α => p.2.foldl min p.1) :=
    Primrec.list_foldl Primrec.snd Primrec.fst
      ((min_primrec hle).comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂
  refine (Primrec.list_casesOn Primrec.id (Primrec.const none)
    (Primrec.option_some.comp (hfold.comp Primrec.snd)).to₂).of_eq ?_
  intro l
  cases l <;> rfl

/-- The ordinary optional list maximum is primitive recursive. -/
theorem list_max?_primrec (hle : PrimrecRel (fun a b : α => a ≤ b)) :
    Primrec (List.max? : List α → Option α) := by
  have hfold : Primrec (fun p : α × List α => p.2.foldl max p.1) :=
    Primrec.list_foldl Primrec.snd Primrec.fst
      ((max_primrec hle).comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂
  refine (Primrec.list_casesOn Primrec.id (Primrec.const none)
    (Primrec.option_some.comp (hfold.comp Primrec.snd)).to₂).of_eq ?_
  intro l
  cases l <;> rfl

/-- Ambient list minimization recovers the finite minimum even though the
canonical list is ordered by codes. -/
theorem finsetView_min?_of_nonempty (s : Finset α) (hs : s.Nonempty) :
    (finsetView s).min? = some (s.min' hs) := by
  apply List.min?_eq_some_iff.mpr
  exact ⟨(mem_finsetView _ _).mpr (s.min'_mem hs),
    fun a ha => s.min'_le a ((mem_finsetView _ _).mp ha)⟩

/-- Ambient list maximization recovers the finite maximum. -/
theorem finsetView_max?_of_nonempty (s : Finset α) (hs : s.Nonempty) :
    (finsetView s).max? = some (s.max' hs) := by
  apply List.max?_eq_some_iff.mpr
  exact ⟨(mem_finsetView _ _).mpr (s.max'_mem hs),
    fun a ha => s.le_max' a ((mem_finsetView _ _).mp ha)⟩

/-- The total finite minimum is exactly optional list minimization followed
by the supplied default, using the unchanged finite-set code's list view. -/
theorem minD_eq_list_min?_getD (s : Finset α) (d : α) :
    minD s d = (finsetView s).min?.getD d := by
  by_cases hs : s.Nonempty
  · rw [minD_of_nonempty s d hs, finsetView_min?_of_nonempty s hs,
      Option.getD_some]
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp [minD, finsetView, multisetView]

/-- The analogous optional-list description of the total finite maximum. -/
theorem maxD_eq_list_max?_getD (s : Finset α) (d : α) :
    maxD s d = (finsetView s).max?.getD d := by
  by_cases hs : s.Nonempty
  · rw [maxD_of_nonempty s d hs, finsetView_max?_of_nonempty s hs,
      Option.getD_some]
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp [maxD, finsetView, multisetView]

/-- A nonempty canonical view computes its ambient minimum by a fold. -/
theorem minD_eq_foldl_of_view_cons (s : Finset α) (d a : α) (l : List α)
    (h : finsetView s = a :: l) : minD s d = l.foldl min a := by
  rw [minD_eq_list_min?_getD, h, List.min?_cons', Option.getD_some]

/-- A nonempty canonical view computes its ambient maximum by a fold. -/
theorem maxD_eq_foldl_of_view_cons (s : Finset α) (d a : α) (l : List α)
    (h : finsetView s = a :: l) : maxD s d = l.foldl max a := by
  rw [maxD_eq_list_max?_getD, h, List.max?_cons', Option.getD_some]

/-- The total finite minimum is primitive recursive in both the supplied
finite set and its default, for a certified ambient comparison. -/
theorem minD_primrec (hle : PrimrecRel (fun a b : α => a ≤ b)) :
    Primrec₂ (@minD α _) :=
  (Primrec.option_getD.comp
    ((list_min?_primrec hle).comp (finsetView_primrec.comp Primrec.fst))
    Primrec.snd).of_eq fun p => (minD_eq_list_min?_getD p.1 p.2).symm

/-- The corresponding uniform certificate for the total finite maximum. -/
theorem maxD_primrec (hle : PrimrecRel (fun a b : α => a ≤ b)) :
    Primrec₂ (@maxD α _) :=
  (Primrec.option_getD.comp
    ((list_max?_primrec hle).comp (finsetView_primrec.comp Primrec.fst))
    Primrec.snd).of_eq fun p => (maxD_eq_list_max?_getD p.1 p.2).symm

end Primitive

end Alexander313.Carlson.PrimitiveFiniteExtrema
