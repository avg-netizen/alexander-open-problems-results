import Alexander313.Carlson.PrimitiveCertificateAlgebra
import Alexander313.Carlson.PrimitiveCertificateAlgebraLaws
import Alexander313.Carlson.FiniteRecognition

/-!
# Uniform primitive-recursive recursive certificate verification

First normalize with the proved original grammar decoder. A second tree fold
computes the actual encoded endpoints and Boolean check. Its internal defaults
are never trusted: the external result rejects every failed original decode.
-/

namespace Alexander313.Carlson.PrimitiveRecursiveChecks

open Encodable Finite PrimitiveCertificateAlgebra
open PrimitiveRecursiveCertificates (atomCode nodeCode)

abbrev Entry := ℕ × Summary × Summary
abbrev Value := Entry × List Entry

def emptySummary : Summary := (0, 0, false)
def emptyEntry : Entry := (0, emptySummary, emptySummary)

def scalar (xs : List Entry) (i : ℕ) : ℕ := (xs.getD i emptyEntry).1
def ruleChild (xs : List Entry) (i : ℕ) : Summary := (xs.getD i emptyEntry).2.1
def chainChild (xs : List Entry) (i : ℕ) : Summary := (xs.getD i emptyEntry).2.2

def ruleStep (n tag : ℕ) (xs : List Entry) : Summary :=
  if tag = 0 then arithmetic n (scalar xs 0) (scalar xs 1)
  else if tag = 1 then downward n (scalar xs 0) (scalar xs 1) (scalar xs 2)
    (scalar xs 3) (scalar xs 4) (scalar xs 5) (scalar xs 6)
  else if tag = 2 then upward n (ruleChild xs 0) (scalar xs 1) (scalar xs 2)
    (scalar xs 3) (scalar xs 4)
  else if tag = 3 then restriction n (chainChild xs 0) (scalar xs 1) (scalar xs 2)
  else if tag = 4 then lifting n (ruleChild xs 0) (scalar xs 1) (scalar xs 2)
    (scalar xs 3) (scalar xs 4)
  else emptySummary

def chainStep (n tag : ℕ) (xs : List Entry) : Summary :=
  if tag = 0 then refl n (scalar xs 0)
  else if tag = 1 then tail (chainChild xs 0) (ruleChild xs 1)
  else emptySummary

variable {σ : Type*} [Primcodable σ]

theorem scalar_primrec {xs : σ → List Entry} {i : σ → ℕ}
    (hx : Primrec xs) (hi : Primrec i) : Primrec (fun s => scalar (xs s) (i s)) :=
  Primrec.fst.comp ((Primrec.list_getD emptyEntry).comp hx hi)

theorem ruleChild_primrec {xs : σ → List Entry} {i : σ → ℕ}
    (hx : Primrec xs) (hi : Primrec i) : Primrec (fun s => ruleChild (xs s) (i s)) :=
  Primrec.fst.comp (Primrec.snd.comp ((Primrec.list_getD emptyEntry).comp hx hi))

theorem chainChild_primrec {xs : σ → List Entry} {i : σ → ℕ}
    (hx : Primrec xs) (hi : Primrec i) : Primrec (fun s => chainChild (xs s) (i s)) :=
  Primrec.snd.comp (Primrec.snd.comp ((Primrec.list_getD emptyEntry).comp hx hi))

theorem ruleStep_primrec {n tag : σ → ℕ} {xs : σ → List Entry}
    (hn : Primrec n) (ht : Primrec tag) (hx : Primrec xs) :
    Primrec (fun s => ruleStep (n s) (tag s) (xs s)) := by
  have hs (i : ℕ) := scalar_primrec hx (Primrec.const i)
  have hr (i : ℕ) := ruleChild_primrec hx (Primrec.const i)
  have hc (i : ℕ) := chainChild_primrec hx (Primrec.const i)
  unfold ruleStep
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0))
    (arithmetic_primrec hn (hs 0) (hs 1))
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 1))
      (downward_primrec hn (hs 0) (hs 1) (hs 2) (hs 3) (hs 4) (hs 5) (hs 6))
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 2))
        (upward_primrec hn (hr 0) (hs 1) (hs 2) (hs 3) (hs 4))
        (Primrec.ite (Primrec.eq.comp ht (Primrec.const 3))
          (restriction_primrec hn (hc 0) (hs 1) (hs 2))
          (Primrec.ite (Primrec.eq.comp ht (Primrec.const 4))
            (lifting_primrec hn (hr 0) (hs 1) (hs 2) (hs 3) (hs 4))
            (Primrec.const emptySummary)))))

theorem chainStep_primrec {n tag : σ → ℕ} {xs : σ → List Entry}
    (hn : Primrec n) (ht : Primrec tag) (hx : Primrec xs) :
    Primrec (fun s => chainStep (n s) (tag s) (xs s)) := by
  unfold chainStep
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0))
    (refl_primrec hn (scalar_primrec hx (Primrec.const 0)))
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 1))
      (tail_primrec (chainChild_primrec hx (Primrec.const 0))
        (ruleChild_primrec hx (Primrec.const 1))) (Primrec.const emptySummary))

def atom (_n x : ℕ) : Value := ((x, emptySummary, emptySummary), [])
def cons (n : ℕ) (h t : Value) : Value :=
  ((0, ruleStep n h.1.1 t.2, chainStep n h.1.1 t.2), h.1 :: t.2)

theorem atom_primrec : Primrec₂ atom :=
  ((Primrec.snd.pair ((Primrec.const emptySummary).pair (Primrec.const emptySummary))).pair
    (Primrec.const [])).to₂

theorem cons_primrec : Primrec (fun p : ℕ × Value × Value => cons p.1 p.2.1 p.2.2) := by
  have hh : Primrec (fun p : ℕ × Value × Value => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have ht : Primrec (fun p : ℕ × Value × Value => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Primrec.const 0).pair
    ((ruleStep_primrec Primrec.fst (Primrec.fst.comp hh) ht).pair
      (chainStep_primrec Primrec.fst (Primrec.fst.comp hh) ht))).pair
    (Primrec.list_cons.comp hh ht)

def evaluate (n code : ℕ) : Value := PrimitiveSExpression.fold atom cons n code
def ruleResult (n code : ℕ) : Summary := (evaluate n code).1.2.1
def chainResult (n code : ℕ) : Summary := (evaluate n code).1.2.2

theorem evaluate_primrec : Primrec₂ evaluate :=
  PrimitiveSExpression.fold_primrec atom_primrec cons_primrec

theorem ruleResult_primrec : Primrec₂ ruleResult :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp evaluate_primrec))).to₂

theorem chainResult_primrec : Primrec₂ chainResult :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp evaluate_primrec))).to₂

@[simp] theorem evaluate_atom (n x : ℕ) : evaluate n (atomCode x) = atom n x :=
  PrimitiveSExpression.fold_atom atom cons n x

theorem evaluate_cons (n h t : ℕ) :
    evaluate n (Nat.pair (h + 1) t) = cons n (evaluate n h) (evaluate n t) :=
  PrimitiveSExpression.fold_cons atom cons n h t

private theorem evaluate_fields (n : ℕ) (fields : List ℕ) :
    (evaluate n (fields.foldr (fun h t => Nat.pair (h + 1) t) (atomCode 0))).2 =
      fields.map (fun c => (evaluate n c).1) := by
  induction fields with
  | nil => simp [atom]
  | cons h t ih =>
      simp only [List.foldr_cons, evaluate_cons]
      simp only [cons, ih, List.map_cons]

theorem ruleResult_node (n tag : ℕ) (fields : List ℕ) :
    ruleResult n (nodeCode tag fields) =
      ruleStep n tag (fields.map (fun c => (evaluate n c).1)) := by
  unfold ruleResult nodeCode
  rw [evaluate_cons]
  simp only [evaluate_atom, atom, cons, evaluate_fields]

theorem chainResult_node (n tag : ℕ) (fields : List ℕ) :
    chainResult n (nodeCode tag fields) =
      chainStep n tag (fields.map (fun c => (evaluate n c).1)) := by
  unfold chainResult nodeCode
  rw [evaluate_cons]
  simp only [evaluate_atom, atom, cons, evaluate_fields]

theorem ruleResult_encode {n : ℕ} (d : RuleCertificate n) :
    ruleResult n (encode d) = ruleSummary d := by
  induction d using RuleCertificate.rec
    (motive_2 := fun c => chainResult n (encode c) = chainSummary c)
  · rename_i P Q
    rw [PrimitiveRecursiveCertificates.encode_arithmetic, ruleResult_node]
    simpa [ruleStep, scalar, atom] using arithmetic_encode P Q
  · rename_i P k a b X N g
    rw [PrimitiveRecursiveCertificates.encode_downward, ruleResult_node]
    simpa [ruleStep, scalar, atom] using downward_encode P k a b X N g
  · rename_i d a b N g ih
    rw [PrimitiveRecursiveCertificates.encode_upward, ruleResult_node]
    change (evaluate n (encode d)).1.2.1 = ruleSummary d at ih
    simpa [ruleStep, scalar, ruleChild, atom, ih] using upward_encode d a b N g
  · rename_i c Q a ih
    rw [PrimitiveRecursiveCertificates.encode_finiteRestriction, ruleResult_node]
    change (evaluate n (encode c)).1.2.2 = chainSummary c at ih
    simpa [ruleStep, scalar, chainChild, atom, ih] using restriction_encode c Q a
  · rename_i d Q Qplus h f ih
    rw [PrimitiveRecursiveCertificates.encode_lifting, ruleResult_node]
    change (evaluate n (encode d)).1.2.1 = ruleSummary d at ih
    simpa [ruleStep, scalar, ruleChild, atom, ih] using lifting_encode d Q Qplus h f
  · rename_i P
    rw [PrimitiveRecursiveCertificates.encode_refl, chainResult_node]
    simpa [chainStep, scalar, atom] using refl_encode P
  · rename_i c d hc hd
    rw [PrimitiveRecursiveCertificates.encode_tail, chainResult_node]
    change (evaluate n (encode c)).1.2.2 = chainSummary c at hc
    change (evaluate n (encode d)).1.2.1 = ruleSummary d at hd
    simpa [chainStep, chainChild, ruleChild, hc, hd] using tail_encode c d

theorem chainResult_encode {n : ℕ} (c : ChainCertificate n) :
    chainResult n (encode c) = chainSummary c := by
  induction c using ChainCertificate.rec (motive_1 := fun _ => True)
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · rename_i P
    rw [PrimitiveRecursiveCertificates.encode_refl, chainResult_node]
    simpa [chainStep, scalar, atom] using refl_encode P
  · rename_i c d hc _
    rw [PrimitiveRecursiveCertificates.encode_tail, chainResult_node]
    change (evaluate n (encode c)).1.2.2 = chainSummary c at hc
    have hd : (evaluate n (encode d)).1.2.1 = ruleSummary d := ruleResult_encode d
    simpa [chainStep, chainChild, ruleChild, hc, hd] using tail_encode c d

/-- Original decoder validation precedes the internal semantic fold. -/
def summarizeRule (n code : ℕ) : Option Summary :=
  (PrimitiveRecursiveCertificates.normalizeRule n code).map (ruleResult n)

def summarizeChain (n code : ℕ) : Option Summary :=
  (PrimitiveRecursiveCertificates.normalizeChain n code).map (chainResult n)

theorem summarizeRule_primrec : Primrec₂ summarizeRule :=
  (Primrec.option_map PrimitiveRecursiveCertificates.normalizeRule_primrec
    (ruleResult_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂

theorem summarizeChain_primrec : Primrec₂ summarizeChain :=
  (Primrec.option_map PrimitiveRecursiveCertificates.normalizeChain_primrec
    (chainResult_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂

/-- All raw inputs use the original decoder, including rejection. -/
theorem summarizeRule_eq (n code : ℕ) :
    summarizeRule n code = (decode (α := RuleCertificate n) code).map ruleSummary := by
  unfold summarizeRule
  rw [PrimitiveRecursiveCertificates.normalizeRule_eq]
  cases decode (α := RuleCertificate n) code <;> simp [ruleResult_encode]

theorem summarizeChain_eq (n code : ℕ) :
    summarizeChain n code = (decode (α := ChainCertificate n) code).map chainSummary := by
  unfold summarizeChain
  rw [PrimitiveRecursiveCertificates.normalizeChain_eq]
  cases decode (α := ChainCertificate n) code <;> simp [chainResult_encode]

@[simp] theorem summarizeRule_encode {n : ℕ} (d : RuleCertificate n) :
    summarizeRule n (encode d) = some (ruleSummary d) := by
  rw [summarizeRule_eq, Encodable.encodek]
  rfl

@[simp] theorem summarizeChain_encode {n : ℕ} (c : ChainCertificate n) :
    summarizeChain n (encode c) = some (chainSummary c) := by
  rw [summarizeChain_eq, Encodable.encodek]
  rfl

/-- Compare the complete encoded endpoint tables, without carrier filtering. -/
def accepts (result : Option Summary) (p q : ℕ) : Bool :=
  (result.map fun r => r.2.2 && decide (r.1 = p ∧ r.2.1 = q)).getD false

theorem accepts_primrec {r : σ → Option Summary} {p q : σ → ℕ}
    (hr : Primrec r) (hp : Primrec p) (hq : Primrec q) :
    Primrec (fun s => accepts (r s) (p s) (q s)) := by
  unfold accepts
  refine Primrec.option_getD.comp (Primrec.option_map hr ?_) (Primrec.const false)
  exact (Primrec.and.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (hp.comp Primrec.fst)).and
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (hq.comp Primrec.fst))).decide).to₂

def checkRule (n p q code : ℕ) : Bool := accepts (summarizeRule n code) p q
def checkChain (n p q code : ℕ) : Bool := accepts (summarizeChain n code) p q

theorem checkRule_primrec {n p q code : σ → ℕ}
    (hn : Primrec n) (hp : Primrec p) (hq : Primrec q) (hc : Primrec code) :
    Primrec (fun s => checkRule (n s) (p s) (q s) (code s)) :=
  accepts_primrec (summarizeRule_primrec.comp hn hc) hp hq

theorem checkChain_primrec {n p q code : σ → ℕ}
    (hn : Primrec n) (hp : Primrec p) (hq : Primrec q) (hc : Primrec code) :
    Primrec (fun s => checkChain (n s) (p s) (q s) (code s)) :=
  accepts_primrec (summarizeChain_primrec.comp hn hc) hp hq

theorem checkRule_encode_endpoints {n : ℕ} (P Q : PatternCode n) (code : ℕ) :
    checkRule n (encode P) (encode Q) code = Finite.checkRule P Q code := by
  unfold checkRule Finite.checkRule
  rw [summarizeRule_eq]
  cases decode (α := RuleCertificate n) code <;> simp [accepts, ruleSummary, encode_inj]

theorem checkChain_encode_endpoints {n : ℕ} (P Q : PatternCode n) (code : ℕ) :
    checkChain n (encode P) (encode Q) code = Finite.checkChain P Q code := by
  unfold checkChain Finite.checkChain
  rw [summarizeChain_eq]
  cases decode (α := ChainCertificate n) code <;> simp [accepts, chainSummary, encode_inj]

theorem rule_summary_program : ∃ machine : Nat.Partrec.Code, ∀ n code : ℕ,
    machine.eval (Nat.pair n code) = Part.some (encode (summarizeRule n code)) := by
  obtain ⟨machine, hm⟩ := PrimitiveRationalPresentation.exists_code summarizeRule_primrec
  exact ⟨machine, fun n code => hm (n, code)⟩

theorem chain_summary_program : ∃ machine : Nat.Partrec.Code, ∀ n code : ℕ,
    machine.eval (Nat.pair n code) = Part.some (encode (summarizeChain n code)) := by
  obtain ⟨machine, hm⟩ := PrimitiveRationalPresentation.exists_code summarizeChain_primrec
  exact ⟨machine, fun n code => hm (n, code)⟩

theorem original_ruleSummary_primrec (n : ℕ) : Primrec (@ruleSummary n) :=
  Primrec.option_some_iff.mp
    ((summarizeRule_primrec.comp (Primrec.const n) Primrec.encode).of_eq
      fun d => summarizeRule_encode d)

theorem original_chainSummary_primrec (n : ℕ) : Primrec (@chainSummary n) :=
  Primrec.option_some_iff.mp
    ((summarizeChain_primrec.comp (Primrec.const n) Primrec.encode).of_eq
      fun c => summarizeChain_encode c)

theorem original_ruleSource_primrec (n : ℕ) : Primrec (@RuleCertificate.source n) :=
  Primrec.encode_iff.mp (Primrec.fst.comp (original_ruleSummary_primrec n))

theorem original_ruleTarget_primrec (n : ℕ) : Primrec (@RuleCertificate.target n) :=
  Primrec.encode_iff.mp (Primrec.fst.comp (Primrec.snd.comp (original_ruleSummary_primrec n)))

theorem original_ruleCheck_primrec (n : ℕ) : Primrec (@RuleCertificate.check n) :=
  Primrec.snd.comp (Primrec.snd.comp (original_ruleSummary_primrec n))

theorem original_chainSource_primrec (n : ℕ) : Primrec (@ChainCertificate.source n) :=
  Primrec.encode_iff.mp (Primrec.fst.comp (original_chainSummary_primrec n))

theorem original_chainTarget_primrec (n : ℕ) : Primrec (@ChainCertificate.target n) :=
  Primrec.encode_iff.mp (Primrec.fst.comp (Primrec.snd.comp (original_chainSummary_primrec n)))

theorem original_chainCheck_primrec (n : ℕ) : Primrec (@ChainCertificate.check n) :=
  Primrec.snd.comp (Primrec.snd.comp (original_chainSummary_primrec n))

end Alexander313.Carlson.PrimitiveRecursiveChecks
