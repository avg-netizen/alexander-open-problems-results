import Alexander313.Wilken.HereditaryFineLocalizationRefinements
import Mathlib.Data.List.Lex

/-!
# Actual argument maximality across a localization interval

Maximal selection is first known only on the root's literal support. The
genuine reversed-argument theta witness and finite hereditary support descent
extend that maximum to EVERY originally admitted weak-normal theta-zero node
between the previous selected value and the root. This is a derived ordinal
interval law, not a support, comparison or spelling oracle. It supplies the
cross-path alignment needed for ordinary lexicographic order. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Localization.OrderSupport

open Localization.Refinements

theorem SourcePath.le_endpoint {r : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : SourcePath r source (c :: tail)) :
    ∀ d ∈ c :: tail, value r d ≤ value r (endpoint (c :: tail)) := by
  induction hp with
  | stop c hc hmax =>
    intro d hd
    simpa only [List.mem_singleton.mp hd, endpoint] using (le_refl (value r c))
  | next c d tail hc hcd hd harg hp ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hcd.le.trans (ih d List.mem_cons_self)
    · exact ih e he

/-- Actual selection bounds arguments throughout the entire ordinal interval,
including nodes absent from the root's literal support. -/
theorem selected_interval_argument_le (r root previous selected : Nat) (tail : List Nat)
    (hr : Node r root) (hp : SourcePath r (support root) (previous :: selected :: tail))
    (a : Nat) (ha : Node r a)
    (hpa : value r previous < value r a) (har : value r a ≤ value r root) :
    argumentValue r a ≤ argumentValue r selected := by
  cases hp with
  | next previous selected tail hprev hps hsel harg hrest =>
    have hs := hrest.nodes selected List.mem_cons_self
    by_contra hnot
    have hsa : argumentValue r selected < argumentValue r a := lt_of_not_ge hnot
    have hm : ∀ e ∈ support root, value r a ≤ value r e →
        argumentValue r e ≤ argumentValue r a :=
      fun e he hae => (harg e he (hpa.trans_le hae)).trans hsa.le
    obtain ⟨e, he, hev⟩ := selected_value_in_support r root a hr ha hm root
      (support_root r root hr) har
    have hen := support_node r root e hr he
    have hea := (node_value_eq_iff_argument_eq r e a hen ha).mp hev
    have hmax : argumentValue r e ≤ argumentValue r selected :=
      harg e he (by rw [hev]; exact hpa)
    exact hsa.not_ge (by rwa [hea] at hmax)

/-- Equality of the interval argument maximum determines the selected value;
there is no claim that it determines a native spelling. -/
theorem selected_interval_argument_lt (r root previous selected : Nat) (tail : List Nat)
    (hr : Node r root) (hp : SourcePath r (support root) (previous :: selected :: tail))
    (a : Nat) (ha : Node r a)
    (hpa : value r previous < value r a) (har : value r a ≤ value r root)
    (hne : value r a ≠ value r selected) :
    argumentValue r a < argumentValue r selected := by
  have hle := selected_interval_argument_le r root previous selected tail hr hp a ha hpa har
  apply lt_of_le_of_ne hle
  intro he
  exact hne ((node_value_eq_iff_argument_eq r a selected ha
    (hp.nodes selected (List.mem_cons_of_mem _ List.mem_cons_self))).mpr he)

/-- Two real selections above equally valued previous nodes cannot reverse
the root order at their first different selected values. -/
theorem selected_cross_order (r left right previous other a b : Nat)
    (xs ys : List Nat) (hl : Node r left) (hr : Node r right)
    (hp : SourcePath r (support left) (previous :: a :: xs))
    (hq : SourcePath r (support right) (other :: b :: ys))
    (hprevious : value r previous = value r other)
    (habound : value r a ≤ value r right) : value r a ≤ value r b := by
  have ha := hp.nodes a (List.mem_cons_of_mem _ List.mem_cons_self)
  have hb := hq.nodes b (List.mem_cons_of_mem _ List.mem_cons_self)
  have hpb := sourcePath_head_lt_tail hq b List.mem_cons_self
  have hpa := sourcePath_head_lt_tail hp a List.mem_cons_self
  by_contra hnot
  have hba : value r b < value r a := lt_of_not_ge hnot
  have hargba := sourcePath_interval_argument_lt hl hp b hb
    (by rw [hprevious]; exact hpb) hba
  have hargab := selected_interval_argument_le r right other b ys hr hq a ha
    (by rw [← hprevious]; exact hpa) habound
  exact hargba.not_ge hargab

end Alexander313.Wilken.RelativeTerm.Hereditary.Localization.OrderSupport
