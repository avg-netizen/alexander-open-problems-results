import Alexander313.Wilken.PublicEpsilonNativeLocalization

/-!
# Actual native localization selections across different supports

The genuine selected support and interval argument laws extend the actual
argument maximum to all checked nodes in the ordinal interval. They align
selections on different literal supports. No support, endpoint, comparison
or representative oracle is supplied. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization.OrderSupport

theorem SourcePath.le_endpoint {q : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : SourcePath q source (c :: tail)) :
    ∀ d ∈ c :: tail, value q d ≤ value q (endpoint (c :: tail)) := by
  induction hp with
  | stop c hc hmax =>
    intro d hd
    simpa only [List.mem_singleton.mp hd, endpoint] using (le_refl (value q c))
  | next c d tail hc hcd hd harg hp ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hcd.le.trans (ih d List.mem_cons_self)
    · exact ih e he

/-- Actual selection bounds arguments throughout the entire ordinal interval,
including nodes absent from the root's literal support. -/
theorem selected_interval_argument_le (q root previous selected : Nat) (tail : List Nat)
    (hr : Node q root) (hp : SourcePath q (support root) (previous :: selected :: tail))
    (a : Nat) (ha : Node q a)
    (hpa : value q previous < value q a) (har : value q a ≤ value q root) :
    argumentValue q a ≤ argumentValue q selected := by
  cases hp with
  | next previous selected tail hprev hps hsel harg hrest =>
    have hs := hrest.nodes selected List.mem_cons_self
    by_contra hnot
    have hsa : argumentValue q selected < argumentValue q a := lt_of_not_ge hnot
    have hm : ∀ e ∈ support root, value q a ≤ value q e →
        argumentValue q e ≤ argumentValue q a :=
      fun e he hae => (harg e he (hpa.trans_le hae)).trans hsa.le
    obtain ⟨e, he, hev⟩ := selected_value_in_support q root a hr ha hm root
      (support_root q root hr) har
    have hen := support_node q root e hr he
    have hea := (node_value_eq_iff_argument_eq q e a hen ha).mp hev
    have hmax : argumentValue q e ≤ argumentValue q selected :=
      harg e he (by rw [hev]; exact hpa)
    exact hsa.not_ge (by rwa [hea] at hmax)

/-- Two real selections above equally valued previous nodes cannot reverse
the root order at their first different selected values. -/
theorem selected_cross_order (q left right previous other a b : Nat)
    (xs ys : List Nat) (hl : Node q left) (hr : Node q right)
    (hp : SourcePath q (support left) (previous :: a :: xs))
    (hq : SourcePath q (support right) (other :: b :: ys))
    (hprevious : value q previous = value q other)
    (habound : value q a ≤ value q right) : value q a ≤ value q b := by
  have ha := hp.nodes a (List.mem_cons_of_mem _ List.mem_cons_self)
  have hb := hq.nodes b (List.mem_cons_of_mem _ List.mem_cons_self)
  have hpb := sourcePath_head_lt_tail hq b List.mem_cons_self
  have hpa := sourcePath_head_lt_tail hp a List.mem_cons_self
  by_contra hnot
  have hba : value q b < value q a := lt_of_not_ge hnot
  have hargba := sourcePath_interval_argument_lt hl hp b hb
    (by rw [hprevious]; exact hpb) hba
  have hargab := selected_interval_argument_le q right other b ys hr hq a ha
    (by rw [← hprevious]; exact hpa) habound
  exact hargba.not_ge hargab

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization.OrderSupport
