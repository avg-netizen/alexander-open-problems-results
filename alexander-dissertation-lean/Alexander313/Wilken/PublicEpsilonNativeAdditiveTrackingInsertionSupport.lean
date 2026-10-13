import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingConditionalReplacement

/-!
# Actual finite replacement table for Definition 3.20.2.2

The original headword is traversed chronologically. Each actual conditional
replacement is executed and stored together with its unchanged original
head code. Finite remaining-list induction derives termination from the
checked headword, the original LOW M factor and its honest bound by the
headword final value. Actual fix induction identifies every stored row with
the corresponding partial replacement execution. No replacement table,
tracking assignment, numerical loop bound or output oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.InsertionSupport

open PublicEpsilonUnboundedIota

abbrev Row := Nat × List Nat
abbrev State := (Nat × Nat) × (List Nat × List Row)

def Matches (q factor head : Nat) (row : Row) : Prop :=
  row.1 = head ∧ row.2 ∈ ConditionalReplacement.execute q head factor

def step (p : State) : Part (List Row ⊕ State) := cond (p.2.1.length == 0)
  (Part.some (Sum.inl p.2.2))
  ((ConditionalReplacement.execute p.1.1 ((p.2.1.head?).getD 0) p.1.2).map fun word =>
    Sum.inr (p.1, (p.2.1.tail, p.2.2 ++ [((p.2.1.head?).getD 0, word)])))

theorem step_partrec : Partrec step := by
  have hq : Primrec (fun p : State => p.1.1) := Primrec.fst.comp Primrec.fst
  have hf : Primrec (fun p : State => p.1.2) := Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : State => p.2.1) := Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun p : State => p.2.2) := Primrec.snd.comp Primrec.snd
  have hh := Primrec.option_getD.comp (Primrec.list_head?.comp hw) (Primrec.const 0)
  have hz := Primrec.beq.comp (Primrec.list_length.comp hw) (Primrec.const 0)
  have he := ConditionalReplacement.execute_partrec.comp ((hq.pair hh).pair hf).to_comp
  have hm : Computable₂ (fun p : State => fun word : List Nat =>
      Sum.inr (p.1, (p.2.1.tail, p.2.2 ++ [((p.2.1.head?).getD 0, word)])) :
        List Row ⊕ State) :=
    (Primrec.sumInr.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.list_tail.comp (hw.comp Primrec.fst)).pair
        (Primrec.list_append.comp (hp.comp Primrec.fst)
          (Primrec.list_cons.comp ((hh.comp Primrec.fst).pair Primrec.snd)
            (Primrec.const [])))))).to_comp.to₂
  exact Partrec.cond hz.to_comp (Primrec.sumInl.comp hp).to_comp.partrec (Partrec.map he hm)

theorem step_nil (q factor : Nat) (prefix : List Row) :
    step ((q, factor), ([], prefix)) = Part.some (Sum.inl prefix) := by
  simp only [step, List.length_nil, beq_self_eq_true, Bool.cond_true]

theorem step_cons (q factor head : Nat) (rest : List Nat) (prefix : List Row) :
    step ((q, factor), (head :: rest, prefix)) =
      (ConditionalReplacement.execute q head factor).map
        (fun word => Sum.inr ((q, factor), (rest, prefix ++ [(head, word)]))) := by
  simp [step]

theorem step_stop (p : State) (out : List Row) (ho : Sum.inl out ∈ step p) :
    p.2.1 = [] ∧ out = p.2.2 := by
  rcases p with ⟨⟨q, factor⟩, heads, prefix⟩
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
      word ∈ ConditionalReplacement.execute p.1.1 head p.1.2 ∧
        next = (p.1, (rest, p.2.2 ++ [(head, word)])) := by
  rcases p with ⟨⟨q, factor⟩, heads, prefix⟩
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

theorem loop_returns (q factor : Nat) (heads : List Nat) (prefix : List Row)
    (hc : ∀ head ∈ heads, ∃ word, word ∈ ConditionalReplacement.execute q head factor) :
    ∃ rows, rows ∈ loop ((q, factor), (heads, prefix)) := by
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
    exact ⟨rows, PFun.mem_fix_iff.mpr (Or.inr ⟨((q, factor), (rest, prefix ++ [(head, word)])),
      by rw [step_cons]; exact Part.mem_map _ hw, hr⟩)⟩

theorem loop_relation (p : State) (out : List Row) (ho : out ∈ loop p) :
    ∃ rows, out = p.2.2 ++ rows ∧ List.Forall₂ (Matches p.1.1 p.1.2) p.2.1 rows := by
  let C : State → Prop := fun s =>
    ∃ rows, out = s.2.2 ++ rows ∧ List.Forall₂ (Matches s.1.1 s.1.2) s.2.1 rows
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

def executeRows (q factor : Nat) (heads : List Nat) : Part (List Row) :=
  loop ((q, factor), (heads, []))

theorem executeRows_partrec : Partrec (fun p : (Nat × Nat) × List Nat =>
    executeRows p.1.1 p.1.2 p.2) :=
  loop_partrec.comp (Primrec.fst.pair (Primrec.snd.pair (Primrec.const []))).to_comp

theorem executeRows_relation (q factor : Nat) (heads : List Nat) (rows : List Row)
    (ho : rows ∈ executeRows q factor heads) : List.Forall₂ (Matches q factor) heads rows := by
  obtain ⟨tail, he, hr⟩ := loop_relation ((q, factor), (heads, [])) rows ho
  have he : rows = tail := by simpa only [List.nil_append] using he
  simpa only [he] using hr

theorem executeRows_returns (q factor : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hb : interpretation q factor ≤ interpretation q (SourceTrackingSequences.lastCode heads)) :
    ∃ rows, rows ∈ executeRows q factor heads :=
  loop_returns q factor heads [] (fun head hhead =>
    ConditionalReplacement.execute_returns q heads hh head factor hhead hf hm hb)

theorem relation_heads (q factor : Nat) {heads : List Nat} {rows : List Row}
    (hr : List.Forall₂ (Matches q factor) heads rows) : rows.map Prod.fst = heads := by
  induction hr with
  | nil => rfl
  | cons he ht ih => simp only [List.map_cons, he.1, ih]

theorem relation_members (q factor : Nat) {heads : List Nat} {rows : List Row}
    (hr : List.Forall₂ (Matches q factor) heads rows) :
    ∀ row ∈ rows, row.1 ∈ heads ∧ row.2 ∈ ConditionalReplacement.execute q row.1 factor := by
  induction hr with
  | nil => intro row hm; exact False.elim (List.not_mem_nil hm)
  | cons he ht ih =>
    intro row hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨by rw [he.1]; exact List.mem_cons_self, by rw [he.1]; exact he.2⟩
    · exact ⟨List.mem_cons_of_mem _ (ih row hm).1, (ih row hm).2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.InsertionSupport
