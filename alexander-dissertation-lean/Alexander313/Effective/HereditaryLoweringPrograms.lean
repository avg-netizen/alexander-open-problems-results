import Alexander313.Wilken.HereditaryLowering

/-!
# Actual Programs for adjacent finite-base lowering

The total code converter and canonical converter execute the constructed PR
algorithm. Positive input and canonical output graph Programs retain the
original admission and the true strict caller bound below the next base.
No arbitrary-base translation or supplied effectivity contract is assumed.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.HereditaryLoweringProgram

open Wilken.RelativeTerm.Hereditary
open Lowering

theorem decisionProgram_exists : ∃ p : Program, ∀ query,
    p.eval query = Part.some (lowerCode query.unpair.1 query.unpair.2) := by
  have h : Partrec (fun query : Nat => Part.some (lowerCode query.unpair.1 query.unpair.2)) :=
    (lowerCode_primrec.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)).to_comp.partrec
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp h)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def decisionProgram : Program := Classical.choose decisionProgram_exists

theorem decisionProgram_eval (r c : Nat) :
    decisionProgram.eval (Nat.pair r c) = Part.some (lowerCode r c) := by
  simpa only [decisionProgram, Nat.unpair_pair] using Classical.choose_spec decisionProgram_exists (Nat.pair r c)

noncomputable def decisionColumn (r : Nat) : Program := decisionProgram.column r

theorem decisionColumn_primrec : Primrec decisionColumn :=
  Program.column_primrec.comp (Primrec.const decisionProgram) Primrec.id

theorem decisionColumn_eval (r c : Nat) :
    (decisionColumn r).eval c = Part.some (lowerCode r c) := by
  rw [decisionColumn, Program.column, Nat.Partrec.Code.eval_curry]
  exact decisionProgram_eval r c

theorem decisionColumn_correct (r c : Nat) (hc : checkInput r c = true) :
    lowCheckCode r (lowerCode r c) = true ∧
      interpretation r (lowerCode r c) = interpretation (r + 1) c := lowerCode_spec r c hc

theorem canonicalProgram_exists : ∃ p : Program, ∀ query,
    p.eval query = Part.some (canonicalLower query.unpair.1 query.unpair.2) := by
  have h : Partrec (fun query : Nat => Part.some (canonicalLower query.unpair.1 query.unpair.2)) :=
    (canonicalLower_primrec.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)).to_comp.partrec
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp h)
  exact ⟨p, fun query => congrFun hp query⟩

noncomputable def canonicalProgram : Program := Classical.choose canonicalProgram_exists

theorem canonicalProgram_eval (r c : Nat) :
    canonicalProgram.eval (Nat.pair r c) = Part.some (canonicalLower r c) := by
  simpa only [canonicalProgram, Nat.unpair_pair] using Classical.choose_spec canonicalProgram_exists (Nat.pair r c)

private theorem positiveProgram_exists (test : Nat → Bool) (ht : Primrec test) :
    ∃ p : Program, ∀ query, p.domain query ↔ test query = true := by
  let constant : Nat → Nat → Bool := fun query _ => test query
  have hc : Primrec₂ constant := (ht.comp Primrec.fst).to₂
  have he : Partrec (fun query => Nat.rfind (fun witness => Part.some (constant query witness))) :=
    Partrec.rfind hc.to_comp.partrec.to₂
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp he)
  refine ⟨p, fun query => ?_⟩
  simp only [Program.domain, hp, constant, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq, exists_const]

private def inputRaw (query : Nat) : Bool := checkInput query.unpair.1 query.unpair.2

private theorem inputRaw_primrec : Primrec inputRaw :=
  checkInput_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

theorem inputProgram_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ inputRaw query = true := positiveProgram_exists inputRaw inputRaw_primrec

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (r c : Nat) : inputProgram.domain (Nat.pair r c) ↔
    checkCode (r + 1) c = true ∧ interpretation (r + 1) c < finiteBase (r + 1) := by
  simpa only [inputProgram, inputRaw, Nat.unpair_pair, checkInput_exact] using
    Classical.choose_spec inputProgram_exists (Nat.pair r c)

noncomputable def inputColumn (r : Nat) : Program := inputProgram.column r

theorem inputColumn_primrec : Primrec inputColumn :=
  Program.column_primrec.comp (Primrec.const inputProgram) Primrec.id

theorem inputColumn_domain (r c : Nat) : (inputColumn r).domain c ↔
    checkCode (r + 1) c = true ∧ interpretation (r + 1) c < finiteBase (r + 1) := by
  rw [inputColumn, Program.column_domain]
  exact inputProgram_domain r c

private def graphRaw (query : Nat) : Bool :=
  graph query.unpair.1.unpair.1 query.unpair.1.unpair.2 query.unpair.2

private theorem graphRaw_primrec : Primrec graphRaw :=
  graph_primrec.comp ((Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)).pair
    (Primrec.snd.comp Primrec.unpair))

theorem graphProgram_exists : ∃ p : Program, ∀ query,
    p.domain query ↔ graphRaw query = true := positiveProgram_exists graphRaw graphRaw_primrec

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (r c q : Nat) : graphProgram.domain (Nat.pair (Nat.pair r c) q) ↔
    checkCode (r + 1) c = true ∧ interpretation (r + 1) c < finiteBase (r + 1) ∧
      Canonical.check q = true ∧ unionInterpretation q = interpretation (r + 1) c := by
  simpa only [graphProgram, graphRaw, Nat.unpair_pair, graph_exact] using
    Classical.choose_spec graphProgram_exists (Nat.pair (Nat.pair r c) q)

noncomputable def graphColumn (r c : Nat) : Program := graphProgram.column (Nat.pair r c)

theorem graphColumn_primrec : Primrec₂ graphColumn :=
  (Program.column_primrec.comp (Primrec.const graphProgram) Primrec₂.natPair).to₂

theorem graphColumn_domain (r c q : Nat) : (graphColumn r c).domain q ↔
    checkCode (r + 1) c = true ∧ interpretation (r + 1) c < finiteBase (r + 1) ∧
      Canonical.check q = true ∧ unionInterpretation q = interpretation (r + 1) c := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain r c q

theorem graphColumn_unique (r c : Nat) (hc : checkInput r c = true) :
    ∃! q, (graphColumn r c).domain q := by
  have hs := (checkInput_exact r c).mp hc
  refine ⟨canonicalLower r c, (graphColumn_domain r c _).mpr
    ⟨hs.1, hs.2, canonicalLower_checked r c hc, canonicalLower_value r c hc⟩, ?_⟩
  intro q hq
  have hg := (graphColumn_domain r c q).mp hq
  exact Canonical.check_value_injective _ _ hg.2.2.1 (canonicalLower_checked r c hc)
    (hg.2.2.2.trans (canonicalLower_value r c hc).symm)

end Alexander313.HereditaryLoweringProgram
