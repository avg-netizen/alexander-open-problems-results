import Alexander313.Wilken.SourceOneNativeAdditiveTrackingConditionalReplacement

/-!
# Actual original source-one finite replacement table

The literal original headword is traversed in order. Each genuine
conditional replacement is executed at the original check-zero dictionary
and paired with its unchanged written head. Finite pending-list induction
derives termination from the original tracking/factor guards and honest
factor<=FINAL bound. Actual fix induction proves every row's provenance.
No table, numerical loop bound, endpoint or tracking-assignment oracle.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.InsertionSupport

abbrev Row := Nat × List Nat
abbrev State := Nat × (List Nat × List Row)

def Matches (factor head : Nat) (row : Row) : Prop :=
  row.1 = head ∧ row.2 ∈ ConditionalReplacement.execute head factor

def step (p : State) : Part (List Row ⊕ State) := cond (p.2.1.length == 0)
  (Part.some (Sum.inl p.2.2))
  ((ConditionalReplacement.execute ((p.2.1.head?).getD 0) p.1).map fun word =>
    Sum.inr (p.1, (p.2.1.tail, p.2.2 ++ [((p.2.1.head?).getD 0, word)])))

theorem step_partrec : Partrec step := by
  have hf : Primrec (fun p : State => p.1) := Primrec.fst
  have hw : Primrec (fun p : State => p.2.1) := Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun p : State => p.2.2) := Primrec.snd.comp Primrec.snd
  have hh := Primrec.option_getD.comp (Primrec.list_head?.comp hw) (Primrec.const 0)
  have hz := Primrec.beq.comp (Primrec.list_length.comp hw) (Primrec.const 0)
  have he := ConditionalReplacement.execute_partrec.comp hh.to_comp hf.to_comp
  have hm : Computable₂ (fun p : State => fun word : List Nat =>
      Sum.inr (p.1, (p.2.1.tail, p.2.2 ++ [((p.2.1.head?).getD 0, word)])) :
        List Row ⊕ State) :=
    (Primrec.sumInr.comp ((hf.comp Primrec.fst).pair
      ((Primrec.list_tail.comp (hw.comp Primrec.fst)).pair
        (Primrec.list_append.comp (hp.comp Primrec.fst)
          (Primrec.list_cons.comp ((hh.comp Primrec.fst).pair Primrec.snd)
            (Primrec.const [])))))).to_comp.to₂
  exact Partrec.cond hz.to_comp (Primrec.sumInl.comp hp).to_comp.partrec (Partrec.map he hm)

theorem step_nil (factor : Nat) (prefix : List Row) :
    step (factor, ([], prefix)) = Part.some (Sum.inl prefix) := by
  simp only [step, List.length_nil, beq_self_eq_true, Bool.cond_true]

theorem step_cons (factor head : Nat) (rest : List Nat) (prefix : List Row) :
    step (factor, (head :: rest, prefix)) =
      (ConditionalReplacement.execute head factor).map
        (fun word => Sum.inr (factor, (rest, prefix ++ [(head, word)]))) := by
  simp [step]

theorem step_stop (p : State) (out : List Row) (ho : Sum.inl out ∈ step p) :
    p.2.1 = [] ∧ out = p.2.2 := by
  rcases p with ⟨factor, heads, prefix⟩
  cases heads with
  | nil =>
    rw [step_nil] at ho
    exact ⟨rfl, by simpa only [Part.mem_some_iff, Sum.inl.injEq] using ho⟩
  | cons head rest =>
    rw [step_cons] at ho
    obtain ⟨word, hw, he⟩ := (Part.mem_map_iff _).mp ho
    simp only [Sum.inr_ne_inl] at he

theorem step_continue (p next : State) (hn : Sum.inr next ∈ step p) :
    ∃ head rest word, p.2.1 = head :: rest ∧
      word ∈ ConditionalReplacement.execute head p.1 ∧
        next = (p.1, (rest, p.2.2 ++ [(head, word)])) := by
  rcases p with ⟨factor, heads, prefix⟩
  cases heads with
  | nil =>
    rw [step_nil] at hn
    simp only [Part.mem_some_iff, Sum.inr_ne_inl] at hn
  | cons head rest =>
    rw [step_cons] at hn
    obtain ⟨word, hw, he⟩ := (Part.mem_map_iff _).mp hn
    exact ⟨head, rest, word, rfl, hw, Sum.inr.inj he.symm⟩

def loop : State → Part (List Row) := PFun.fix step

theorem loop_partrec : Partrec loop := Partrec.fix step_partrec

theorem loop_returns (factor : Nat) (heads : List Nat) (prefix : List Row)
    (hc : ∀ head ∈ heads, ∃ word, word ∈ ConditionalReplacement.execute head factor) :
    ∃ rows, rows ∈ loop (factor, (heads, prefix)) := by
  revert prefix hc
  induction heads with
  | nil =>
    intro prefix hc
    exact ⟨prefix, PFun.mem_fix_iff.mpr (Or.inl (by rw [step_nil]; exact Part.mem_some _))⟩
  | cons head rest ih =>
    intro prefix hc
    obtain ⟨word, hw⟩ := hc head List.mem_cons_self
    obtain ⟨rows, hr⟩ := ih (prefix ++ [(head, word)])
      (fun a ha => hc a (List.mem_cons_of_mem _ ha))
    exact ⟨rows, PFun.mem_fix_iff.mpr (Or.inr ⟨(factor, (rest, prefix ++ [(head, word)])),
      by rw [step_cons]; exact Part.mem_map _ hw, hr⟩)⟩

theorem loop_relation (p : State) (out : List Row) (ho : out ∈ loop p) :
    ∃ rows, out = p.2.2 ++ rows ∧ List.Forall₂ (Matches p.1) p.2.1 rows := by
  let C : State → Prop := fun s =>
    ∃ rows, out = s.2.2 ++ rows ∧ List.Forall₂ (Matches s.1) s.2.1 rows
  have h : C p := by
    apply PFun.fixInduction (C := C) ho
    intro s hs ih
    rcases PFun.mem_fix_iff.mp hs with hstop | ⟨next, hn, hout⟩
    · obtain ⟨hnil, he⟩ := step_stop s out hstop
      exact ⟨[], by simpa only [List.append_nil] using he, by rw [hnil]; exact .nil⟩
    · obtain ⟨head, rest, word, hheads, hw, hnext⟩ := step_continue s next hn
      obtain ⟨rows, he, hrel⟩ := ih next hn
      rw [hnext] at he hrel
      refine ⟨(head, word) :: rows, ?_, ?_⟩
      · simpa only [List.append_assoc, List.singleton_append] using he
      · rw [hheads]; exact .cons ⟨rfl, hw⟩ hrel
  exact h

def executeRows (factor : Nat) (heads : List Nat) : Part (List Row) :=
  loop (factor, (heads, []))

theorem executeRows_partrec : Partrec₂ executeRows :=
  (loop_partrec.comp (Primrec.fst.pair (Primrec.snd.pair (Primrec.const []))).to_comp).to₂

theorem executeRows_relation (factor : Nat) (heads : List Nat) (rows : List Row)
    (ho : rows ∈ executeRows factor heads) : List.Forall₂ (Matches factor) heads rows := by
  obtain ⟨tail, he, hr⟩ := loop_relation (factor, (heads, [])) rows ho
  have he : rows = tail := by simpa only [List.nil_append] using he
  simpa only [he] using hr

theorem executeRows_returns (factor : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (NativeContext.SourceTrackingSequences.lastCode heads)) :
    ∃ rows, rows ∈ executeRows factor heads :=
  loop_returns factor heads [] (fun head hhead =>
    ConditionalReplacement.execute_returns heads hh head factor hhead hf hm hb)

theorem relation_heads (factor : Nat) {heads : List Nat} {rows : List Row}
    (hr : List.Forall₂ (Matches factor) heads rows) : rows.map Prod.fst = heads := by
  induction hr with
  | nil => rfl
  | cons he ht ih => simp only [List.map_cons, he.1, ih]

theorem relation_members (factor : Nat) {heads : List Nat} {rows : List Row}
    (hr : List.Forall₂ (Matches factor) heads rows) :
    ∀ row ∈ rows, row.1 ∈ heads ∧ row.2 ∈ ConditionalReplacement.execute row.1 factor := by
  induction hr with
  | nil => intro row hm; exact False.elim (List.not_mem_nil hm)
  | cons he ht ih =>
    intro row hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨by rw [he.1]; exact List.mem_cons_self, by rw [he.1]; exact he.2⟩
    · exact ⟨List.mem_cons_of_mem _ (ih row hm).1, (ih row hm).2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.InsertionSupport
