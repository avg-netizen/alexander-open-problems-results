import Alexander313.RecordedMain
import Alexander313.ShapeCoding

/-!
# Finite representatives for one shared recorded main table

The mask is represented by literal source formulas whose shapes are the
protected arguments. A single finite key/label table represents arbitrary
labels on all queries of both the source sentence and its distinguished atom.
Repeated queries have the same owner/whole-shape key. No hereditary condition,
source-row condition, guard, marker condition or admissibility test is removed.
-/

namespace Alexander313

namespace Shape

def toFormula {Owner : Type} : Shape Owner → Formula Owner
  | .falsum => .falsum
  | .equal => .equal .zero .zero
  | .imp φ ψ => .imp φ.toFormula ψ.toFormula
  | .conj φ ψ => .conj φ.toFormula ψ.toFormula
  | .disj φ ψ => .disj φ.toFormula ψ.toFormula
  | .neg φ => .neg φ.toFormula
  | .all φ => .all 0 φ.toFormula
  | .ex φ => .ex 0 φ.toFormula
  | .know a φ => .know a φ.toFormula

@[simp] theorem shape_toFormula {Owner : Type} (sh : Shape Owner) :
    sh.toFormula.shape = sh := by
  induction sh <;> simp_all [toFormula, Formula.shape]

end Shape

namespace Formula

def queryList {Owner : Type} : Formula Owner → List (Owner × Shape Owner)
  | .falsum => []
  | .equal _ _ => []
  | .imp φ ψ => φ.queryList ++ ψ.queryList
  | .conj φ ψ => φ.queryList ++ ψ.queryList
  | .disj φ ψ => φ.queryList ++ ψ.queryList
  | .neg φ => φ.queryList
  | .all _ φ => φ.queryList
  | .ex _ φ => φ.queryList
  | .know a φ => (a, φ.shape) :: φ.queryList

@[simp] theorem mem_queryList {Owner : Type} [DecidableEq Owner]
    (φ : Formula Owner) (q : Owner × Shape Owner) :
    q ∈ φ.queryList ↔ q ∈ φ.queries := by
  induction φ <;> simp_all [queryList, queries]

theorem record_congr_on_queries {Owner Label : Type} [DecidableEq Owner]
    (φ : Formula Owner) (head₁ head₂ : Owner → Shape Owner → RecordedHead Owner Label)
    (agree : ∀ a sh, (a, sh) ∈ φ.queries → head₁ a sh = head₂ a sh) :
    φ.record head₁ = φ.record head₂ := by
  revert agree
  induction φ with
  | falsum => intro _; rfl
  | equal t u => intro _; rfl
  | imp φ ψ ihφ ihψ =>
    intro h
    have hl := ihφ (fun a sh hm => h a sh (Finset.mem_union_left _ hm))
    have hr := ihψ (fun a sh hm => h a sh (Finset.mem_union_right _ hm))
    simp only [record, hl, hr]
  | conj φ ψ ihφ ihψ =>
    intro h
    have hl := ihφ (fun a sh hm => h a sh (Finset.mem_union_left _ hm))
    have hr := ihψ (fun a sh hm => h a sh (Finset.mem_union_right _ hm))
    simp only [record, hl, hr]
  | disj φ ψ ihφ ihψ =>
    intro h
    have hl := ihφ (fun a sh hm => h a sh (Finset.mem_union_left _ hm))
    have hr := ihψ (fun a sh hm => h a sh (Finset.mem_union_right _ hm))
    simp only [record, hl, hr]
  | neg φ ih => intro h; exact congrArg Formula.neg (ih h)
  | all x φ ih => intro h; exact congrArg (Formula.all x) (ih h)
  | ex x φ ih => intro h; exact congrArg (Formula.ex x) (ih h)
  | know a φ ih =>
    intro h
    have hh := h a φ.shape (Finset.mem_insert_self _ _)
    have hb := ih (fun b sh hm => h b sh (Finset.mem_insert_of_mem hm))
    simp only [record, hh, hb]

end Formula

namespace RecordedTable

abbrev Mask := List (Nat × Formula Nat)
abbrev Labels := List (Nat × Nat)

def mask (M : Mask) : Finset (Nat × Shape Nat) :=
  (M.map (fun p => (p.1, p.2.shape))).toFinset

@[simp] theorem mem_mask (M : Mask) (a : Nat) (sh : Shape Nat) :
    (a, sh) ∈ mask M ↔ ∃ φ : Formula Nat, (a, φ) ∈ M ∧ φ.shape = sh := by
  simp only [mask, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨b, φ⟩, hp, he⟩
    have hb : b = a := congrArg Prod.fst he
    have hs : φ.shape = sh := congrArg Prod.snd he
    subst b
    exact ⟨φ, hp, hs⟩
  · rintro ⟨φ, hp, hs⟩
    exact ⟨(a, φ), hp, by simp only [hs]⟩

noncomputable def representatives (H : Finset (Nat × Shape Nat)) : Mask :=
  H.toList.map (fun p => (p.1, p.2.toFormula))

@[simp] theorem mask_representatives (H : Finset (Nat × Shape Nat)) :
    mask (representatives H) = H := by
  ext q
  rcases q with ⟨a, sh⟩
  simp only [mask, representatives, List.map_map, Function.comp_def,
    Shape.shape_toFormula, List.mem_toFinset, Finset.mem_toList]
  simp

theorem mask_representative_exists (H : Finset (Nat × Shape Nat)) :
    ∃ M : Mask, mask M = H := ⟨representatives H, mask_representatives H⟩

def lookup {Label : Type} (default : Label) (T : List (Nat × Label)) (key : Nat) : Label :=
  T.foldr (fun p value => if p.1 = key then p.2 else value) default

def queryKey (a : Nat) (sh : Shape Nat) : Nat := Nat.pair a sh.code

theorem queryKey_injective :
    Function.Injective (fun p : Nat × Shape Nat => queryKey p.1 p.2) := by
  rintro ⟨a, sh⟩ ⟨b, sub⟩ h
  have he := Nat.pair_eq_pair.mp h
  exact Prod.ext he.1 (Shape.code_injective he.2)

def listLabelTable {Label : Type} (labels : Nat → Shape Nat → Label)
    (Q : List (Nat × Shape Nat)) : List (Nat × Label) :=
  Q.map (fun p => (queryKey p.1 p.2, labels p.1 p.2))

theorem lookup_listLabelTable {Label : Type} (default : Label)
    (labels : Nat → Shape Nat → Label) (Q : List (Nat × Shape Nat))
    (q : Nat × Shape Nat) (hq : q ∈ Q) :
    lookup default (listLabelTable labels Q) (queryKey q.1 q.2) = labels q.1 q.2 := by
  revert hq
  induction Q with
  | nil => intro hq; simp at hq
  | cons p Q ih =>
    intro hq
    by_cases hk : queryKey p.1 p.2 = queryKey q.1 q.2
    · have hpq : p = q := queryKey_injective hk
      subst q
      simp [lookup, listLabelTable]
    · have ht : q ∈ Q := by
        rcases List.mem_cons.mp hq with hp | ht
        · subst q
          exact (hk rfl).elim
        · exact ht
      simpa only [listLabelTable, List.map_cons, lookup, List.foldr_cons, hk, ↓reduceIte]
        using ih ht

noncomputable def labelTable {Label : Type} (labels : Nat → Shape Nat → Label)
    (Q : Finset (Nat × Shape Nat)) : List (Nat × Label) := listLabelTable labels Q.toList

theorem lookup_labelTable {Label : Type} (default : Label)
    (labels : Nat → Shape Nat → Label) (Q : Finset (Nat × Shape Nat))
    (a : Nat) (sh : Shape Nat) (hq : (a, sh) ∈ Q) :
    lookup default (labelTable labels Q) (queryKey a sh) = labels a sh :=
  lookup_listLabelTable default labels Q.toList (a, sh) (Finset.mem_toList.mpr hq)

def heads {Label : Type} (A E : Finset Nat) (M : Mask)
    (default : Label) (T : List (Nat × Label)) :
    Nat → Shape Nat → RecordedHead Nat Label :=
  mainHeads A E (mask M) (fun a sh => lookup default T (queryKey a sh))

theorem record_heads_labelTable {Label : Type} (A E : Finset Nat) (M : Mask)
    (default : Label) (labels : Nat → Shape Nat → Label)
    (Q : Finset (Nat × Shape Nat)) (σ : Formula Nat) (hq : σ.queries ⊆ Q) :
    σ.record (heads A E M default (labelTable labels Q)) =
      σ.record (mainHeads A E (mask M) labels) := by
  apply Formula.record_congr_on_queries
  intro a sh hm
  simp only [heads, mainHeads, maskedHeads]
  rw [lookup_labelTable default labels Q a sh (hq hm)]

end RecordedTable

/-- Every witness is finite, with one supplied default and one shared label
table. The formulas in the mask are representatives of full argument shapes. -/
def RecordedFiniteMain {Label : Type} [DecidableEq Label] [LT Label]
    (default : Label) {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (A E : Finset Nat) (a : Nat) (R₁ R₂ : Label → Label → Prop)
    (φ : Formula (RecordedHead Nat Label)) : Prop :=
  ∃ (σ atom : Formula Nat) (M : RecordedTable.Mask)
    (T : List (Nat × Label)) (ms : List (Label × Nat)),
    RecordedMainSource C A E a σ atom ∧ HereditaryQueries (RecordedTable.mask M) ∧
    Disjoint A E ∧ (ms.map Prod.snd).Nodup ∧
    (∀ p ∈ ms, (markerTag Nat p.2).shape ∉ σ.shape.subshapes) ∧
    (atom.record (RecordedTable.heads A E M default T)).MainGuarded R₁ R₂ E (markerPoints ms) ∧
    φ = markerPadding a ms (σ.record (RecordedTable.heads A E M default T)) ∧
    φ.RecordedAdmissible A E

theorem RecordedFiniteMain_exact {Label : Type} [DecidableEq Label] [LT Label]
    (default : Label) {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (A E : Finset Nat) (a : Nat) (R₁ R₂ : Label → Label → Prop)
    (φ : Formula (RecordedHead Nat Label)) :
    RecordedFiniteMain default C A E a R₁ R₂ φ ↔ RecordedMain C A E a R₁ R₂ φ := by
  constructor
  · rintro ⟨σ, atom, M, T, ms, hs, hh, hd, hn, hf, hg, he, ha⟩
    exact ⟨σ, atom, RecordedTable.mask M,
      (fun b sh => RecordedTable.lookup default T (RecordedTable.queryKey b sh)), ms,
      hs, hh, hd, hn, hf, hg, he, ha⟩
  · rintro ⟨σ, atom, H, labels, ms, hs, hh, hd, hn, hf, hg, he, ha⟩
    obtain ⟨M, hM⟩ := RecordedTable.mask_representative_exists H
    let Q := σ.queries ∪ atom.queries
    let T := RecordedTable.labelTable labels Q
    have hσ : σ.record (RecordedTable.heads A E M default T) =
        σ.record (mainHeads A E H labels) := by
      rw [← hM]
      exact RecordedTable.record_heads_labelTable A E M default labels Q σ
        Finset.subset_union_left
    have hatom : atom.record (RecordedTable.heads A E M default T) =
        atom.record (mainHeads A E H labels) := by
      rw [← hM]
      exact RecordedTable.record_heads_labelTable A E M default labels Q atom
        Finset.subset_union_right
    refine ⟨σ, atom, M, T, ms, hs, ?_, hd, hn, hf, ?_, ?_, ha⟩
    · simpa only [hM] using hh
    · simpa only [hatom] using hg
    · exact he.trans (congrArg (markerPadding a ms) hσ.symm)

end Alexander313
