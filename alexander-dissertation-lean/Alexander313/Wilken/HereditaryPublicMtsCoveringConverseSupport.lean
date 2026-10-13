import Alexander313.Wilken.HereditaryPublicMtsCovering

/-!
# Actual stored words contain only their chronological input entries

Induction follows the literal table rows. A selected row supplies its
already computed word, and the actual update adds only the current input.
The fallback is the original root singleton. Thus every entry of every
stored word is an actual root or localization input, without a supplied
path or representation. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.CoveringConverseSupport

theorem rows_word_members {root : Nat} {inputs : List Nat} {es : List Support.Entry}
    (hr : Support.Rows root inputs es) :
    ∀ e ∈ es, ∀ c ∈ e.2, c ∈ root :: inputs := by
  induction hr with
  | initial =>
    intro e he c hc
    have heq : e = (root, [root]) := List.mem_singleton.mp he
    subst e
    exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hc))
  | append inputs es current hr ih =>
    intro e he c hc
    have hinclude : ∀ a ∈ root :: inputs, a ∈ root :: (inputs ++ [current]) := by
      intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · exact List.mem_cons.mpr (Or.inl ha)
      · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl ha)))
    rcases List.mem_append.mp he with he | he
    · exact hinclude c (ih e he c hc)
    · have heq : e = (current, Support.extend root current es) := List.mem_singleton.mp he
      subst e
      cases hs : Support.select current es with
      | none =>
        have he : c = root := by
          simpa only [Support.extend_none root current es hs, List.mem_singleton] using hc
        exact List.mem_cons.mpr (Or.inl he)
      | some chosen =>
        have hc' : c ∈ chosen.2 ++ [current] := by
          simpa only [Support.extend_some root current es chosen hs] using hc
        rcases List.mem_append.mp hc' with hc' | hc'
        · exact hinclude c (ih chosen (Support.select_mem current es chosen hs) c hc')
        · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr hc')))

theorem table_word_members (root : Nat) (inputs : List Nat) :
    ∀ e ∈ Support.table root inputs, ∀ c ∈ e.2, c ∈ root :: inputs :=
  rows_word_members (Support.table_rows root inputs)

theorem word_members (root : Nat) (inputs : List Nat) :
    ∀ c ∈ Support.word root inputs, c ∈ root :: inputs := by
  cases inputs with
  | nil =>
    intro c hc
    simpa only [Support.word_nil] using hc
  | cons a rest =>
    have hne : a :: rest ≠ [] := List.cons_ne_nil _ _
    obtain ⟨last, hs, _⟩ := Hereditary.FinePredecessor.stripLast_split (a :: rest) hne
    have hrow : (last, Support.word root (a :: rest)) ∈ Support.table root (a :: rest) := by
      rw [hs, Support.table_append_singleton, Support.word_append]
      exact List.mem_append.mpr (Or.inr List.mem_cons_self)
    exact table_word_members root (a :: rest) _ hrow

theorem covering_current_mem {root current : Nat} {codes : List Nat}
    (hc : CoveringSupport.Covering root current codes) : current ∈ codes := by
  cases hc with
  | root hr => exact List.mem_cons_self
  | append previous current codes hp hnext =>
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicMts.CoveringConverseSupport
