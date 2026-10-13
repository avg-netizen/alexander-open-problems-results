import Alexander313.Wilken.HereditaryEvaluationLastLongBlock
import Alexander313.Wilken.HereditaryMultiplication

/-!
# Actual ordered numerical multiplier products for Definition 3.35

The partial recursive finite loop multiplies the literal chronological
factor list using the existing genuine canonical ordinal multiplication.
Its output is canonical, has exactly the ordered product value, and exists
exactly when every factor is an original public code. The actual final MNF
execution therefore constructs beta-prime from its literal tail. No tail
product code, arithmetic graph or multiplication result is supplied.
Source-only uncompiled candidates; evaluator recursion remains separate.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationMultiplierProduct

open Alexander313.Wilken.MultiplicativeNormalForm (factorProduct)

abbrev State := Nat × List Nat

def step (s : State) : Part (Nat ⊕ State) := cond (s.2.length == 0)
  (Part.some (Sum.inl s.1))
  ((Multiplication.multiply s.1 ((s.2.head?).getD 0)).map
    (fun next => Sum.inr (next, s.2.tail)))

theorem step_partrec : Partrec step := by
  have ha : Primrec (fun s : State => s.1) := Primrec.fst
  have hx : Primrec (fun s : State => s.2) := Primrec.snd
  have hh := Primrec.option_getD.comp (Primrec.list_head?.comp hx) (Primrec.const 0)
  have hz := Primrec.beq.comp (Primrec.list_length.comp hx) (Primrec.const 0)
  have hm := Multiplication.multiply_partrec.comp ha.to_comp hh.to_comp
  have hc : Computable₂ (fun s : State => fun next : Nat =>
      Sum.inr (next, s.2.tail) : Nat ⊕ State) :=
    (Primrec.sumInr.comp (Primrec.snd.pair
      (Primrec.list_tail.comp (Primrec.snd.comp Primrec.fst)))).to_comp.to₂
  exact Partrec.cond hz.to_comp (Primrec.sumInl.comp ha).to_comp.partrec (Partrec.map hm hc)

theorem step_nil (acc : Nat) : step (acc, []) = Part.some (Sum.inl acc) := by
  simp only [step, List.length_nil, beq_self_eq_true, Bool.cond_true]

theorem step_cons (acc factor : Nat) (factors : List Nat) :
    step (acc, factor :: factors) = (Multiplication.multiply acc factor).map
      (fun next => Sum.inr (next, factors)) := by
  simp [step]

def loop : State → Part Nat := PFun.fix step

theorem loop_partrec : Partrec loop := Partrec.fix step_partrec

/-- Every real finite execution derives the admission of every factor,
canonical output and ordered product, rather than assuming arithmetic. -/
theorem loop_spec (acc : Nat) (factors : List Nat) (out : Nat)
    (ha : Canonical.check acc = true) (ho : out ∈ loop (acc, factors)) :
    (∀ factor ∈ factors, unionCheck factor = true) ∧ Canonical.check out = true ∧
      unionInterpretation out = unionInterpretation acc * factorProduct (factors.map unionInterpretation) := by
  induction factors generalizing acc out with
  | nil =>
    rcases PFun.mem_fix_iff.mp ho with hs | ⟨next, hn, hout⟩
    · rw [step_nil] at hs
      have he : out = acc := by simpa only [Part.mem_some_iff, Sum.inl.injEq] using hs
      subst out
      exact ⟨fun factor hm => False.elim (List.not_mem_nil hm), ha, by
        simp only [List.map_nil, factorProduct, mul_one]⟩
    · rw [step_nil] at hn
      simp only [Part.mem_some_iff, Sum.inr_ne_inl] at hn
  | cons factor factors ih =>
    rcases PFun.mem_fix_iff.mp ho with hs | ⟨state, hn, hout⟩
    · rw [step_cons] at hs
      obtain ⟨next, hm, he⟩ := (Part.mem_map_iff _).mp hs
      simp only [Sum.inr_ne_inl] at he
    · rw [step_cons] at hn
      obtain ⟨next, hm, he⟩ := (Part.mem_map_iff _).mp hn
      have hstate : (next, factors) = state := Sum.inr.inj he
      rw [← hstate] at hout
      have hp := Multiplication.multiply_value acc factor next hm
      obtain ⟨hrest, hc, hv⟩ := ih next out hp.2.2.1 hout
      refine ⟨?_, hc, ?_⟩
      · intro c hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hp.2.1
        · exact hrest c hm
      · rw [hv, hp.2.2.2, List.map_cons]
        change (unionInterpretation acc * unionInterpretation factor) *
          factorProduct (factors.map unionInterpretation) =
          unionInterpretation acc * (unionInterpretation factor * factorProduct (factors.map unionInterpretation))
        exact mul_assoc _ _ _

theorem loop_returns (acc : Nat) (factors : List Nat)
    (ha : Canonical.check acc = true) (hf : ∀ factor ∈ factors, unionCheck factor = true) :
    ∃ out, out ∈ loop (acc, factors) := by
  induction factors generalizing acc with
  | nil =>
    refine ⟨acc, PFun.mem_fix_iff.mpr (Or.inl ?_)⟩
    rw [step_nil]
    exact Part.mem_some _
  | cons factor factors ih =>
    obtain ⟨next, hm, hc, hv⟩ := Multiplication.multiply_returns acc factor
      (Canonical.check_original ha) (hf factor List.mem_cons_self)
    obtain ⟨out, ho⟩ := ih next hc (fun c hm => hf c (List.mem_cons_of_mem factor hm))
    refine ⟨out, PFun.mem_fix_iff.mpr (Or.inr ⟨(next, factors), ?_, ho⟩)⟩
    rw [step_cons]
    exact Part.mem_map _ hm

def execute (factors : List Nat) : Part Nat := loop (MultiplicativeNormalForm.oneCode, factors)

theorem execute_partrec : Partrec execute :=
  loop_partrec.comp ((Primrec.const MultiplicativeNormalForm.oneCode).pair Primrec.id).to_comp

theorem execute_spec (factors : List Nat) (out : Nat) (ho : out ∈ execute factors) :
    (∀ factor ∈ factors, unionCheck factor = true) ∧ Canonical.check out = true ∧
      unionInterpretation out = factorProduct (factors.map unionInterpretation) := by
  have hs := loop_spec _ factors out MultiplicativeNormalForm.oneCode_checked ho
  refine ⟨hs.1, hs.2.1, ?_⟩
  simpa only [MultiplicativeNormalForm.oneCode_value, one_mul] using hs.2.2

theorem execute_domain (factors : List Nat) :
    (execute factors).Dom ↔ ∀ factor ∈ factors, unionCheck factor = true := by
  constructor
  · intro h
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp h
    exact (execute_spec factors out ho).1
  · intro h
    exact Part.dom_iff_mem.mpr (loop_returns _ factors MultiplicativeNormalForm.oneCode_checked h)

/-- Actual MNF execution constructs the genuine beta-prime code from
all factors after the first, including canonical one for an empty tail. -/
theorem final_factors_tail_returns (beta : Nat) (factors : List Nat)
    (hf : factors ∈ EvaluationFinalComponentSupport.factors beta) :
    ∃ rest, rest ∈ execute factors.tail ∧ Canonical.check rest = true ∧
      unionInterpretation rest = factorProduct (factors.tail.map unionInterpretation) := by
  have hs := EvaluationFinalComponentSupport.factors_spec beta factors hf
  have ht : ∀ factor ∈ factors.tail, unionCheck factor = true := fun factor hm =>
    Canonical.check_original (hs.2.1 factor (List.mem_of_mem_tail hm))
  obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp ((execute_domain factors.tail).mpr ht)
  exact ⟨out, ho, (execute_spec factors.tail out ho).2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationMultiplierProduct
