import Alexander313.RecordedReconstruction

/-!
# Finite hereditary live/ghost choices

Queries are determined by the source skeleton. The complete query set of a
target is hereditary: keeping an external argument of that target also keeps
every external argument inside it. A finite mask therefore keeps all term
variants and numerical instances, including nested occurrences under any head.

This supplies the concrete mode-table part of note 24's π_H. The active
stratifier is independent and is passed as a head table for the other owners.
It does not assert effective ordinal guard room or stage soundness.
-/

namespace Alexander313

namespace Shape

variable {Owner : Type} [DecidableEq Owner]

def queries : Shape Owner → Finset (Owner × Shape Owner)
  | .falsum => ∅
  | .equal => ∅
  | .imp φ ψ => φ.queries ∪ ψ.queries
  | .conj φ ψ => φ.queries ∪ ψ.queries
  | .disj φ ψ => φ.queries ∪ ψ.queries
  | .neg φ => φ.queries
  | .all φ => φ.queries
  | .ex φ => φ.queries
  | .know a φ => insert (a, φ) φ.queries

theorem queries_hereditary (sh : Shape Owner) (a : Owner) (sub : Shape Owner)
    (h : (a, sub) ∈ sh.queries) : sub.queries ⊆ sh.queries := by
  induction sh with
  | falsum => simp [queries] at h
  | equal => simp [queries] at h
  | imp φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp h with hφ | hψ
    · exact fun _ hm => Finset.mem_union.mpr (Or.inl (ihφ hφ hm))
    · exact fun _ hm => Finset.mem_union.mpr (Or.inr (ihψ hψ hm))
  | conj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp h with hφ | hψ
    · exact fun _ hm => Finset.mem_union.mpr (Or.inl (ihφ hφ hm))
    · exact fun _ hm => Finset.mem_union.mpr (Or.inr (ihψ hψ hm))
  | disj φ ψ ihφ ihψ =>
    rcases Finset.mem_union.mp h with hφ | hψ
    · exact fun _ hm => Finset.mem_union.mpr (Or.inl (ihφ hφ hm))
    · exact fun _ hm => Finset.mem_union.mpr (Or.inr (ihψ hψ hm))
  | neg φ ih => exact ih h
  | all φ ih => exact ih h
  | ex φ ih => exact ih h
  | know b φ ih =>
    rcases Finset.mem_insert.mp h with heq | hsub
    · have hs : sub = φ := congrArg Prod.snd heq
      subst sub
      exact fun _ hm => Finset.mem_insert_of_mem hm
    · exact fun _ hm => Finset.mem_insert_of_mem (ih hsub hm)

end Shape

namespace Formula

variable {Owner : Type} [DecidableEq Owner]

@[simp] theorem queries_shape (φ : Formula Owner) : φ.shape.queries = φ.queries := by
  induction φ <;> simp_all [shape, Shape.queries, queries]

theorem queries_hereditary (φ : Formula Owner) (a : Owner) (sh : Shape Owner)
    (h : (a, sh) ∈ φ.queries) : sh.queries ⊆ φ.queries := by
  simpa only [queries_shape] using
    Shape.queries_hereditary φ.shape a sh (by simpa only [queries_shape] using h)

end Formula

def HereditaryQueries {Owner : Type} [DecidableEq Owner]
    (H : Finset (Owner × Shape Owner)) : Prop :=
  ∀ a sh, (a, sh) ∈ H → sh.queries ⊆ H

theorem target_queries_hereditary {Owner : Type} [DecidableEq Owner]
    (φ : Formula Owner) : HereditaryQueries φ.queries :=
  fun a sh h => φ.queries_hereditary a sh h

def maskedHeads {Owner Label : Type} [DecidableEq Owner]
    (E : Finset Owner) (H : Finset (Owner × Shape Owner))
    (active : Owner → Shape Owner → RecordedHead Owner Label)
    (a : Owner) (sh : Shape Owner) : RecordedHead Owner Label :=
  if a ∈ E then
    if (a, sh) ∈ H then .live a else .ghost a
  else active a sh

theorem maskedHeads_erase {Owner Label : Type} [DecidableEq Owner]
    (E : Finset Owner) (H : Finset (Owner × Shape Owner))
    (active : Owner → Shape Owner → RecordedHead Owner Label)
    (ha : ∀ a sh, (active a sh).erase = a) (a : Owner) (sh : Shape Owner) :
    (maskedHeads E H active a sh).erase = a := by
  by_cases he : a ∈ E
  · by_cases hh : (a, sh) ∈ H <;> simp [maskedHeads, he, hh, RecordedHead.erase]
  · simp only [maskedHeads, he, ↓reduceIte, ha]

theorem maskedHeads_live {Owner Label : Type} [DecidableEq Owner]
    (E : Finset Owner) (H : Finset (Owner × Shape Owner))
    (active : Owner → Shape Owner → RecordedHead Owner Label)
    (a : Owner) (sh : Shape Owner) (he : a ∈ E) (hh : (a, sh) ∈ H) :
    maskedHeads E H active a sh = .live a := by
  simp only [maskedHeads, he, hh, ↓reduceIte]

theorem maskedHeads_ghost {Owner Label : Type} [DecidableEq Owner]
    (E : Finset Owner) (H : Finset (Owner × Shape Owner))
    (active : Owner → Shape Owner → RecordedHead Owner Label)
    (a : Owner) (sh : Shape Owner) (he : a ∈ E) (hh : (a, sh) ∉ H) :
    maskedHeads E H active a sh = .ghost a := by
  simp only [maskedHeads, he, hh, ↓reduceIte]

theorem maskedHeads_kept_subtree {Owner Label : Type} [DecidableEq Owner]
    (E : Finset Owner) (H : Finset (Owner × Shape Owner))
    (active : Owner → Shape Owner → RecordedHead Owner Label)
    (hereditary : HereditaryQueries H)
    (a b : Owner) (sh sub : Shape Owner)
    (ha : (a, sh) ∈ H) (hb : b ∈ E) (hsub : (b, sub) ∈ sh.queries) :
    maskedHeads E H active b sub = .live b :=
  maskedHeads_live E H active b sub hb (hereditary a sh ha hsub)

theorem maskedHeads_target_external {Owner Label : Type} [DecidableEq Owner]
    (E : Finset Owner) (active : Owner → Shape Owner → RecordedHead Owner Label)
    (φ : Formula Owner) (a : Owner) (sh : Shape Owner)
    (ha : a ∈ E) (hquery : (a, sh) ∈ φ.queries) :
    maskedHeads E φ.queries active a sh = .live a :=
  maskedHeads_live E φ.queries active a sh ha hquery

theorem maskedHeads_target_subtree {Owner Label : Type} [DecidableEq Owner]
    (E : Finset Owner) (active : Owner → Shape Owner → RecordedHead Owner Label)
    (φ : Formula Owner) (a b : Owner) (sh sub : Shape Owner)
    (hquery : (a, sh) ∈ φ.queries) (hb : b ∈ E) (hsub : (b, sub) ∈ sh.queries) :
    maskedHeads E φ.queries active b sub = .live b :=
  maskedHeads_kept_subtree E φ.queries active (target_queries_hereditary φ)
    a b sh sub hquery hb hsub

end Alexander313
