import Alexander313.Wilken.HereditaryEvaluationRelativeCallers
import Alexander313.Wilken.HereditaryMuCoveredRelativePublicFidelity

/-!
# Concrete finite relative components of Definition3.35

A genuine partial-recursive finite traversal executes each relative
assignment at its literal previous epsilon, starting at endpointCode m.
The independent epsilon reference and true initial source gap derive all
calls. Exact fix induction identifies every stored component, and every
actual component has an independent public Tracking certificate. Its
computed lengths are exactly the lengths of these real words. The final
MNF component, uniform height bound, lexical descent and evaluation o
remain separate constructions. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationBlocks

open EvaluationRelativeCallers
open GlobalTrackingSequences

/-- The literal starting code represents the printed alpha0=1+upsilon_m,
including the genuine source convention upsilon_0=0. -/
theorem initial_value (m : Nat) :
    unionInterpretation (endpointCode m) = 1 + sourceUpsilon (m : Ordinal.{0}) := by
  cases m with
  | zero =>
    simp only [PublicEpsilonSourceDictionary.endpointCode_value, finiteBase_zero,
      Nat.cast_zero, sourceUpsilon_zero, add_zero]
  | succ n =>
    have hi := GlobalMuDictionary.Support.endpoint_input n
    have hp := epsilon_principal _ hi
    have hv : unionInterpretation (endpointCode (n + 1)) =
        sourceUpsilon ((n + 1 : Nat) : Ordinal.{0}) :=
      (PublicEpsilonSourceDictionary.endpointCode_value _).trans
        (PublicUpsilonSegment.successor_value n).symm
    rw [← hv]
    exact (hp.2.2.add_eq_right
      (EpsilonOffsets.epsilon_one_lt ((GlobalMuDictionary.Support.inputCheck_exact _).mp hi).2)).symm

abbrev Block := List Nat
abbrev State := Nat × (List Nat × List Block)

inductive Assigned : Nat → List Nat → List Block → Prop
  | nil (gamma : Nat) : Assigned gamma [] []
  | cons (gamma beta : Nat) (rest : List Nat) (word : Block) (words : List Block)
      (hw : word ∈ blockExecute gamma beta) (ht : Assigned beta rest words) :
      Assigned gamma (beta :: rest) (word :: words)

inductive CallerChain : Nat → List Nat → Prop
  | nil (gamma : Nat) : CallerChain gamma []
  | cons (gamma beta : Nat) (rest : List Nat)
      (hi : blockInputCheck gamma beta = true) (ht : CallerChain beta rest) :
      CallerChain gamma (beta :: rest)

def step (s : State) : Part (List Block ⊕ State) := cond (s.2.1.length == 0)
  (Part.some (Sum.inl s.2.2))
  ((blockExecute s.1 ((s.2.1.head?).getD 0)).map fun word =>
    Sum.inr (((s.2.1.head?).getD 0), (s.2.1.tail, s.2.2 ++ [word])))

theorem step_partrec : Partrec step := by
  have hg : Primrec (fun s : State => s.1) := Primrec.fst
  have hx : Primrec (fun s : State => s.2.1) := Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun s : State => s.2.2) := Primrec.snd.comp Primrec.snd
  have hb := Primrec.option_getD.comp (Primrec.list_head?.comp hx) (Primrec.const 0)
  have hz := Primrec.beq.comp (Primrec.list_length.comp hx) (Primrec.const 0)
  have he := blockExecute_partrec.comp hg.to_comp hb.to_comp
  have hm : Computable₂ (fun s : State => fun word : Block =>
      Sum.inr (((s.2.1.head?).getD 0), (s.2.1.tail, s.2.2 ++ [word])) :
        List Block ⊕ State) :=
    (Primrec.sumInr.comp ((hb.comp Primrec.fst).pair
      ((Primrec.list_tail.comp (hx.comp Primrec.fst)).pair
        (Primrec.list_append.comp (hp.comp Primrec.fst)
          (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))))).to_comp.to₂
  exact Partrec.cond hz.to_comp (Primrec.sumInl.comp hp).to_comp.partrec (Partrec.map he hm)

theorem step_nil (gamma : Nat) (prefix : List Block) :
    step (gamma, ([], prefix)) = Part.some (Sum.inl prefix) := by
  simp only [step, List.length_nil, beq_self_eq_true, Bool.cond_true]

theorem step_cons (gamma beta : Nat) (rest : List Nat) (prefix : List Block) :
    step (gamma, (beta :: rest, prefix)) =
      (blockExecute gamma beta).map (fun word => Sum.inr (beta, (rest, prefix ++ [word]))) := by
  simp [step]

theorem step_stop (s : State) (out : List Block) (ho : Sum.inl out ∈ step s) :
    s.2.1 = [] ∧ out = s.2.2 := by
  rcases s with ⟨gamma, inputs, prefix⟩
  cases inputs with
  | nil =>
    rw [step_nil] at ho
    exact ⟨rfl, by simpa only [Part.mem_some_iff, Sum.inl.injEq] using ho⟩
  | cons beta rest =>
    rw [step_cons] at ho
    obtain ⟨word, hw, he⟩ := (Part.mem_map_iff _).mp ho
    simp only [Sum.inr_ne_inl] at he

theorem step_continue (s next : State) (hn : Sum.inr next ∈ step s) :
    ∃ beta rest word, s.2.1 = beta :: rest ∧ word ∈ blockExecute s.1 beta ∧
      next = (beta, (rest, s.2.2 ++ [word])) := by
  rcases s with ⟨gamma, inputs, prefix⟩
  cases inputs with
  | nil =>
    rw [step_nil] at hn
    simp only [Part.mem_some_iff, Sum.inr_ne_inl] at hn
  | cons beta rest =>
    rw [step_cons] at hn
    obtain ⟨word, hw, he⟩ := (Part.mem_map_iff _).mp hn
    exact ⟨beta, rest, word, rfl, hw, Sum.inr.inj he.symm⟩

def loop : State → Part (List Block) := PFun.fix step

theorem loop_partrec : Partrec loop := Partrec.fix step_partrec

theorem loop_relation (s : State) (out : List Block) (ho : out ∈ loop s) :
    ∃ words, out = s.2.2 ++ words ∧ Assigned s.1 s.2.1 words := by
  let C : State → Prop := fun t =>
    ∃ words, out = t.2.2 ++ words ∧ Assigned t.1 t.2.1 words
  have h : C s := by
    apply PFun.fixInduction (C := C) ho
    intro t ht ih
    rcases PFun.mem_fix_iff.mp ht with hstop | ⟨next, hn, hout⟩
    · obtain ⟨hnil, he⟩ := step_stop t out hstop
      exact ⟨[], by simpa only [List.append_nil] using he, by rw [hnil]; exact .nil _⟩
    · obtain ⟨beta, rest, word, hinputs, hw, hnext⟩ := step_continue t next hn
      obtain ⟨words, he, ha⟩ := ih next hn
      rw [hnext] at he ha
      refine ⟨word :: words, ?_, ?_⟩
      · simpa only [List.append_assoc, List.singleton_append] using he
      · rw [hinputs]; exact .cons _ _ _ _ _ hw ha
  exact h

theorem loop_returns_assigned {gamma : Nat} {inputs : List Nat} {words : List Block}
    (ha : Assigned gamma inputs words) (prefix : List Block) :
    prefix ++ words ∈ loop (gamma, (inputs, prefix)) := by
  induction ha generalizing prefix with
  | nil gamma =>
    rw [List.append_nil]
    exact PFun.mem_fix_iff.mpr (Or.inl (by rw [step_nil]; exact Part.mem_some prefix))
  | cons gamma beta rest word words hw ht ih =>
    apply PFun.mem_fix_iff.mpr
    refine Or.inr ⟨(beta, (rest, prefix ++ [word])), ?_, ?_⟩
    · rw [step_cons]
      exact Part.mem_map _ hw
    · simpa only [List.append_assoc, List.singleton_append] using ih (prefix ++ [word])

def execute (gamma : Nat) (inputs : List Nat) : Part (List Block) := loop (gamma, (inputs, []))

theorem execute_partrec : Partrec₂ execute :=
  (loop_partrec.comp (Primrec.fst.pair (Primrec.snd.pair (Primrec.const []))).to_comp).to₂

theorem execute_graph (gamma : Nat) (inputs : List Nat) (words : List Block) :
    words ∈ execute gamma inputs ↔ Assigned gamma inputs words := by
  constructor
  · intro ho
    obtain ⟨actual, he, ha⟩ := loop_relation (gamma, (inputs, [])) words ho
    have he : words = actual := by simpa only [List.nil_append] using he
    simpa only [he] using ha
  · intro ha
    simpa only [List.nil_append] using loop_returns_assigned ha []

theorem callers_returns {gamma : Nat} {inputs : List Nat} (hc : CallerChain gamma inputs) :
    ∃ words, words ∈ execute gamma inputs := by
  induction hc with
  | nil gamma => exact ⟨[], (execute_graph gamma [] []).mpr (.nil gamma)⟩
  | cons gamma beta rest hi ht ih =>
    obtain ⟨word, hw⟩ := blockExecute_returns gamma beta hi
    obtain ⟨words, hs⟩ := ih
    exact ⟨word :: words, (execute_graph _ _ _).mpr
      (.cons _ _ _ _ _ hw ((execute_graph _ _ _).mp hs))⟩

theorem reference_callers (a : Nat) (rest : List Nat) (hr : EpsilonReference (a :: rest)) :
    CallerChain a rest := by
  induction rest generalizing a with
  | nil => exact .nil a
  | cons b xs ih =>
    exact .cons a b xs (adjacent_caller a b xs hr) (ih b (reference_tail a (b :: xs) hr))

theorem global_callers (m : Nat) (tail : List Nat) (hr : EpsilonReference tail)
    (hg : TailGap m tail) : CallerChain (endpointCode m) tail := by
  cases tail with
  | nil => exact .nil _
  | cons a xs =>
    exact .cons _ a xs (initial_caller m a xs hr hg) (reference_callers a xs hr)

/-- A genuine finite global reference derives all real component
executions, even for an empty proper-epsilon tail. -/
theorem global_returns (m : Nat) (tail : List Nat) (hr : EpsilonReference tail)
    (hg : TailGap m tail) : ∃ words, words ∈ execute (endpointCode m) tail :=
  callers_returns (global_callers m tail hr hg)

theorem block_tracking (gamma beta : Nat) (word : Block)
    (ho : word ∈ blockExecute gamma beta) : PublicTrackingSequences.Tracking word := by
  cases he : (gamma == endpointCode 0) with
  | true =>
    have h : word ∈ SourceOneRelativeAssignment.execute beta := by
      simpa only [blockExecute, he, Bool.cond_true] using ho
    exact SourceOneRelativeAssignment.execute_tracking beta word h
  | false =>
    have h : word ∈ MuCoveredRelativeAssignment.execute gamma beta := by
      simpa only [blockExecute, he, Bool.cond_false] using ho
    exact NativeContext.PublicEpsilonUnboundedIota.CoveredPublicMu.execute_tracking gamma beta word h

theorem assigned_tracking {gamma : Nat} {inputs : List Nat} {words : List Block}
    (ha : Assigned gamma inputs words) : ∀ word ∈ words, PublicTrackingSequences.Tracking word := by
  induction ha with
  | nil gamma => intro word hw; exact False.elim (List.not_mem_nil hw)
  | cons gamma beta rest word words hw ht ih =>
    intro current hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact block_tracking gamma beta word hw
    · exact ih current hc

theorem assigned_length {gamma : Nat} {inputs : List Nat} {words : List Block}
    (ha : Assigned gamma inputs words) : words.length = inputs.length := by
  induction ha with
  | nil gamma => rfl
  | cons gamma beta rest word words hw ht ih => simp only [List.length_cons, ih]

def lengths (words : List Block) : List Nat := words.map List.length

theorem lengths_primrec : Primrec lengths :=
  Primrec.list_map Primrec.id (Primrec.list_length.comp Primrec.snd).to₂

def executeLengths (gamma : Nat) (inputs : List Nat) : Part (List Nat) :=
  (execute gamma inputs).map lengths

theorem executeLengths_partrec : Partrec₂ executeLengths :=
  (Partrec.map execute_partrec (lengths_primrec.to_comp.comp Computable.snd).to₂).to₂

theorem executeLengths_graph (gamma : Nat) (inputs ns : List Nat) :
    ns ∈ executeLengths gamma inputs ↔
      ∃ words, Assigned gamma inputs words ∧ lengths words = ns := by
  rw [executeLengths, Part.mem_map_iff]
  constructor
  · rintro ⟨words, hw, he⟩
    exact ⟨words, (execute_graph gamma inputs words).mp hw, he⟩
  · rintro ⟨words, ha, he⟩
    exact ⟨words, (execute_graph gamma inputs words).mpr ha, he⟩

/-- Exactly one positive length is computed for each genuine proper-tail
entry, from actual assignments with independent public certificates. -/
theorem executeLengths_spec (gamma : Nat) (inputs ns : List Nat)
    (ho : ns ∈ executeLengths gamma inputs) :
    ns.length = inputs.length ∧ ∀ n ∈ ns, 0 < n := by
  obtain ⟨words, ha, he⟩ := (executeLengths_graph gamma inputs ns).mp ho
  refine ⟨?_, ?_⟩
  · rw [← he, lengths, List.length_map]
    exact assigned_length ha
  · intro n hn
    rw [← he, lengths] at hn
    obtain ⟨word, hw, rfl⟩ := List.mem_map.mp hn
    have hne := (assigned_tracking ha word hw).1
    cases word with
    | nil => exact False.elim (hne rfl)
    | cons a xs => simp only [List.length_cons]; omega

theorem global_lengths_returns (m : Nat) (tail : List Nat) (hr : EpsilonReference tail)
    (hg : TailGap m tail) : ∃ ns, ns ∈ executeLengths (endpointCode m) tail := by
  obtain ⟨words, hw⟩ := global_returns m tail hr hg
  exact ⟨lengths words, Part.mem_map lengths hw⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationBlocks
