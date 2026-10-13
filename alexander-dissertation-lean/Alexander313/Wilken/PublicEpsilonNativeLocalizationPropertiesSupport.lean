import Alexander313.Wilken.PublicEpsilonNativeLocalization

/-!
# Value-prefix locality for the genuine original coded-epsilon localization

The actual greatest-ARGUMENT source recurrence has a unique ordinal-value
path, even when a full-support witness has a different written spelling.
Genuine selected support and hereditary written support prove that every
prefix is this recurrence over its own endpoint. These are actual original
native-q Nodes and comparators; no value-prefix or spelling oracle is
supplied. Literal code equality is not inferred from ordinal equality.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization.Properties

open ThetaCourse

theorem sourcePath_arguments_descending {q : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : SourcePath q source (c :: tail)) :
    (tail.map (argumentValue q)).Pairwise (fun a b => b < a) := by
  induction hp with
  | stop c hc hmax => simp only [List.map_nil, List.pairwise_nil]
  | next c d tail hc hcd hd harg hp ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    have hde := sourcePath_head_lt_tail hp e he
    have heNode := hp.nodes e (List.mem_cons_of_mem _ he)
    have hdNode := hp.nodes d List.mem_cons_self
    have hle := harg e (sourcePath_tail_mem hp e he) (hcd.trans hde)
    apply lt_of_le_of_ne hle
    intro heq
    have hvalue := (node_value_eq_iff_argument_eq q e d heNode hdNode).mpr heq
    exact hvalue.symm.not_lt hde

theorem nativePath_arguments_descending (q c : Nat) (hc : inputCheck q c = true) :
    ((nativePath q c).tail.map (argumentValue q)).Pairwise (fun a b => b < a) := by
  obtain ⟨tail, he⟩ := nativePath_head q c
  have hp := nativePath_source q c hc
  rw [he] at hp ⊢
  simpa only [List.tail_cons] using sourcePath_arguments_descending hp

theorem sourcePath_suffix {q : Nat} {source path : List Nat}
    (hp : SourcePath q source path) («prefix» : List Nat) (c : Nat) (tail : List Nat)
    (he : path = «prefix» ++ c :: tail) : SourcePath q source (c :: tail) := by
  revert path
  induction «prefix» with
  | nil => intro path hp he; simpa only [List.nil_append, he] using hp
  | cons a «prefix» ih =>
    intro path hp he
    cases hp with
    | stop d hd hmax =>
      have hlen := congrArg List.length he
      simp only [List.length_singleton, List.length_append, List.length_cons] at hlen
      omega
    | next d e rest hd hde hes harg hrest =>
      have hcons : d :: e :: rest = a :: («prefix» ++ c :: tail) := by
        simpa only [List.cons_append] using he
      exact ih (path := e :: rest) hrest (List.cons.inj hcons).2

/-- The source recurrence with membership by actual value. This permits the
genuine support witness to have another native spelling. -/
inductive ValuePath (q : Nat) (source : List Nat) : List Nat → Prop
  | stop (c : Nat) (hc : Node q c) (hmax : ∀ d ∈ source, value q d ≤ value q c) :
      ValuePath q source [c]
  | next (c d : Nat) (tail : List Nat) (hc : Node q c) (hcd : value q c < value q d)
      (hd : ∃ e ∈ source, value q e = value q d)
      (harg : ∀ e ∈ source, value q c < value q e → argumentValue q e ≤ argumentValue q d)
      (hrest : ValuePath q source (d :: tail)) : ValuePath q source (c :: d :: tail)

theorem sourcePath_valuePath {q : Nat} {source path : List Nat}
    (hp : SourcePath q source path) : ValuePath q source path := by
  induction hp with
  | stop c hc hmax => exact ValuePath.stop c hc hmax
  | next c d tail hc hcd hd harg hp ih =>
    exact ValuePath.next c d tail hc hcd ⟨d, hd, rfl⟩ harg ih

theorem ValuePath.nodes {q : Nat} {source path : List Nat} (hp : ValuePath q source path) :
    ∀ c ∈ path, Node q c := by
  induction hp with
  | stop c hc hmax => intro d hd; rw [List.mem_singleton.mp hd]; exact hc
  | next c d tail hc hcd hd harg hp ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hc
    · exact ih e he

/-- Maximal actual argument determines the entire value path, independently
of ties between native spellings. -/
theorem ValuePath.values_unique {q : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : ValuePath q source (c :: tail)) (hs : ∀ e ∈ source, Node q e)
    (d : Nat) (rest : List Nat) (hq : ValuePath q source (d :: rest))
    (he : value q c = value q d) :
    ((c :: tail).map (value q)) = ((d :: rest).map (value q)) := by
  revert d rest
  induction hp with
  | stop c hc hmax =>
    intro d rest hq he
    cases hq with
    | stop d hd hstop => simp only [List.map_cons, List.map_nil, he]
    | next d f rest hd hdf hf harg hrest =>
      obtain ⟨e, hes, hef⟩ := hf
      have hbound : value q f ≤ value q c := by rw [← hef]; exact hmax e hes
      exact False.elim ((he.trans_lt hdf).not_ge hbound)
  | next c e tail hc hce heSource harg hrest ih =>
    intro d rest hq he
    have hen := hrest.nodes e List.mem_cons_self
    cases hq with
    | stop d hd hstop =>
      obtain ⟨a, has, hae⟩ := heSource
      have hbound : value q e ≤ value q d := by rw [← hae]; exact hstop a has
      exact False.elim ((he.symm.trans_lt hce).not_ge hbound)
    | next d f rest hd hdf hfSource hfarg hfrest =>
      have hfn := hfrest.nodes f List.mem_cons_self
      obtain ⟨a, has, hae⟩ := heSource
      obtain ⟨b, hbs, hbf⟩ := hfSource
      have haa := (node_value_eq_iff_argument_eq q a e (hs a has) hen).mp hae
      have hbb := (node_value_eq_iff_argument_eq q b f (hs b hbs) hfn).mp hbf
      have hfe : argumentValue q f ≤ argumentValue q e := by
        rw [← hbb]
        apply harg b hbs
        rw [hbf]
        exact he.trans_lt hdf
      have hef : argumentValue q e ≤ argumentValue q f := by
        rw [← haa]
        apply hfarg a has
        rw [hae]
        exact he.symm.trans_lt hce
      have heValue := (node_value_eq_iff_argument_eq q e f hen hfn).mpr (le_antisymm hef hfe)
      have htail := ih f rest hfrest heValue
      simp only [List.map_cons, he, htail]

/-- Each prefix is the actual source recurrence over its own endpoint's full
support, with membership by value where an earlier spelling differs. -/
theorem sourcePath_prefix_valuePath {q root : Nat} {path : List Nat}
    (hroot : Node q root) (hp : SourcePath q (support root) path)
    («prefix» : List Nat) (d : Nat) (suffix : List Nat) (he : path = «prefix» ++ d :: suffix) :
    ValuePath q (support d) («prefix» ++ [d]) := by
  revert path
  induction «prefix» with
  | nil =>
    intro path hp he
    simp only [List.nil_append] at he ⊢
    rw [he] at hp
    have hd := hp.nodes d List.mem_cons_self
    exact ValuePath.stop d hd (fun e he => support_bound q d e hd he)
  | cons a «prefix» ih =>
    intro path hp he
    cases hp with
    | stop c hc hmax =>
      have hlen := congrArg List.length he
      simp only [List.length_singleton, List.length_append, List.length_cons] at hlen
      omega
    | next c e tail hc hce hes harg hrest =>
      have hcons : c :: e :: tail = a :: («prefix» ++ d :: suffix) := by
        simpa only [List.cons_append] using he
      have hca := (List.cons.inj hcons).1
      subst a
      have htail := (List.cons.inj hcons).2
      have hdTail : d ∈ e :: tail := by
        rw [htail]
        exact List.mem_append.mpr (Or.inr List.mem_cons_self)
      have hdSource := sourcePath_tail_mem
        (SourcePath.next c e tail hc hce hes harg hrest) d hdTail
      have hwitness := sourcePath_selected_support hroot
        (SourcePath.next c e tail hc hce hes harg hrest) d hdTail
      have hprefix := ih (path := e :: tail) hrest htail
      have hhead : ∃ rest : List Nat, «prefix» ++ [d] = e :: rest := by
        cases «prefix» with
        | nil =>
          have hed : e = d := (List.cons.inj htail).1
          rw [← hed]
          exact ⟨[], rfl⟩
        | cons b «prefix» =>
          have heb : e = b := (List.cons.inj htail).1
          rw [← heb]
          exact ⟨«prefix» ++ [d], rfl⟩
      obtain ⟨rest, hhead⟩ := hhead
      rw [hhead] at hprefix
      have hrestricted : ∀ b ∈ support d, value q c < value q b →
          argumentValue q b ≤ argumentValue q e := fun b hb hcb =>
        harg b (support_trans q root d b hroot hdSource hb) hcb
      simpa only [List.cons_append, hhead] using
        ValuePath.next c e rest hc hce hwitness hrestricted hprefix

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization.Properties
