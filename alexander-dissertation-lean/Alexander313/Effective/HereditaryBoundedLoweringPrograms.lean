import Alexander313.Wilken.HereditaryBoundedLowering

/-!
# Actual bounded finite-level lowering Programs

The native and canonical total Programs execute the constructed PR bounded
descent. A guarded Program halts exactly on r<=s, original admission at s,
and the true strict endpoint bound. Positive input and canonical graph
Programs retain that domain. Every compiler specializes a genuine fixed
kernel primitive recursively. Native output stays normal at the requested
level; canonical union output is unique by true ordinal value. No arbitrary
temporary-base translation is claimed. All proofs remain uncompiled.
-/

namespace Alexander313.HereditaryBoundedLoweringProgram

open Wilken.RelativeTerm.Hereditary

def inputTuple (query : Nat) : Nat × (Nat × Nat) := (query.unpair.1, query.unpair.2.unpair)

theorem inputTuple_primrec : Primrec inputTuple :=
  (Primrec.fst.comp Primrec.unpair).pair (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

theorem nativeProgram_exists : ∃ p : Program, ∀ query,
    p.eval query = Part.some (BoundedLowering.lowerCode query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2) :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp
    (BoundedLowering.lowerCode_primrec.comp inputTuple_primrec).to_comp.partrec)

noncomputable def nativeProgram : Program := Classical.choose nativeProgram_exists

theorem nativeProgram_eval (r s c : Nat) : nativeProgram.eval (Nat.pair r (Nat.pair s c)) =
    Part.some (BoundedLowering.lowerCode r s c) := by
  simpa only [Nat.unpair_pair] using Classical.choose_spec nativeProgram_exists (Nat.pair r (Nat.pair s c))

theorem nativeProgram_correct (r s c : Nat) (h : BoundedLowering.checkInput r s c = true) :
    Theta.acceptedLowCode r (BoundedLowering.lowerCode r s c) = true ∧
      interpretation r (BoundedLowering.lowerCode r s c) = interpretation s c :=
  BoundedLowering.lowerCode_spec r s c h

theorem canonicalProgram_exists : ∃ p : Program, ∀ query,
    p.eval query = Part.some (BoundedLowering.canonicalLower query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2) :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp
    (BoundedLowering.canonicalLower_primrec.comp inputTuple_primrec).to_comp.partrec)

noncomputable def canonicalProgram : Program := Classical.choose canonicalProgram_exists

theorem canonicalProgram_eval (r s c : Nat) : canonicalProgram.eval (Nat.pair r (Nat.pair s c)) =
    Part.some (BoundedLowering.canonicalLower r s c) := by
  simpa only [Nat.unpair_pair] using Classical.choose_spec canonicalProgram_exists (Nat.pair r (Nat.pair s c))

theorem canonicalProgram_correct (r s c : Nat) (h : BoundedLowering.checkInput r s c = true) :
    Canonical.check (BoundedLowering.canonicalLower r s c) = true ∧
      unionInterpretation (BoundedLowering.canonicalLower r s c) = interpretation s c :=
  ⟨BoundedLowering.canonicalLower_checked r s c h, BoundedLowering.canonicalLower_value r s c h⟩

noncomputable def nativeColumn (r s : Nat) : Program := (nativeProgram.column r).column s

theorem nativeColumn_primrec : Primrec₂ nativeColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const nativeProgram) Primrec.fst) Primrec.snd).to₂

theorem nativeColumn_eval (r s c : Nat) : (nativeColumn r s).eval c = Part.some (BoundedLowering.lowerCode r s c) := by
  simp only [nativeColumn, Nat.Partrec.Code.eval_curry, nativeProgram_eval]

noncomputable def canonicalColumn (r s : Nat) : Program := (canonicalProgram.column r).column s

theorem canonicalColumn_primrec : Primrec₂ canonicalColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const canonicalProgram) Primrec.fst) Primrec.snd).to₂

theorem canonicalColumn_eval (r s c : Nat) : (canonicalColumn r s).eval c = Part.some (BoundedLowering.canonicalLower r s c) := by
  simp only [canonicalColumn, Nat.Partrec.Code.eval_curry, canonicalProgram_eval]

theorem guardedProgram_exists : ∃ p : Program, ∀ query,
    p.eval query = BoundedLowering.lower query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2 :=
  Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp (BoundedLowering.lower_partrec.comp inputTuple_primrec.to_comp))

noncomputable def guardedProgram : Program := Classical.choose guardedProgram_exists

theorem guardedProgram_eval (r s c : Nat) : guardedProgram.eval (Nat.pair r (Nat.pair s c)) = BoundedLowering.lower r s c := by
  simpa only [Nat.unpair_pair] using Classical.choose_spec guardedProgram_exists (Nat.pair r (Nat.pair s c))

theorem guardedProgram_domain (r s c : Nat) : guardedProgram.domain (Nat.pair r (Nat.pair s c)) ↔
    r ≤ s ∧ checkCode s c = true ∧ interpretation s c < finiteBase (r + 1) := by
  simp only [Program.domain, guardedProgram_eval, BoundedLowering.lower_domain]

theorem guardedProgram_graph_iff (r s c q : Nat) : q ∈ guardedProgram.eval (Nat.pair r (Nat.pair s c)) ↔
    r ≤ s ∧ checkCode s c = true ∧ interpretation s c < finiteBase (r + 1) ∧
      Canonical.check q = true ∧ unionInterpretation q = interpretation s c := by
  rw [guardedProgram_eval, BoundedLowering.lower_graph_iff, BoundedLowering.graph_exact]

noncomputable def guardedColumn (r s : Nat) : Program := (guardedProgram.column r).column s

theorem guardedColumn_primrec : Primrec₂ guardedColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const guardedProgram) Primrec.fst) Primrec.snd).to₂

theorem guardedColumn_domain (r s c : Nat) : (guardedColumn r s).domain c ↔
    r ≤ s ∧ checkCode s c = true ∧ interpretation s c < finiteBase (r + 1) := by
  rw [guardedColumn, Program.column_domain, Program.column_domain]
  exact guardedProgram_domain r s c

private theorem positiveProgram_exists (test : Nat → Bool) (ht : Primrec test) :
    ∃ p : Program, ∀ query, p.domain query ↔ test query = true := by
  let constant : Nat → Nat → Bool := fun query _ => test query
  have hc : Primrec₂ constant := (ht.comp Primrec.fst).to₂
  have he : Partrec (fun query => Nat.rfind (fun witness => Part.some (constant query witness))) :=
    Partrec.rfind hc.to_comp.partrec.to₂
  obtain ⟨p, hp⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp he)
  refine ⟨p, fun query => ?_⟩
  simp [Program.domain, hp, constant, Nat.rfind_dom, eq_comm]

def inputRaw (query : Nat) : Bool := BoundedLowering.checkInput query.unpair.1 query.unpair.2.unpair.1 query.unpair.2.unpair.2

theorem inputRaw_primrec : Primrec inputRaw := BoundedLowering.checkInput_primrec.comp inputTuple_primrec

theorem inputProgram_exists : ∃ p : Program, ∀ query, p.domain query ↔ inputRaw query = true :=
  positiveProgram_exists inputRaw inputRaw_primrec

noncomputable def inputProgram : Program := Classical.choose inputProgram_exists

theorem inputProgram_domain (r s c : Nat) : inputProgram.domain (Nat.pair r (Nat.pair s c)) ↔
    r ≤ s ∧ checkCode s c = true ∧ interpretation s c < finiteBase (r + 1) := by
  simpa only [inputRaw, Nat.unpair_pair, BoundedLowering.checkInput_exact] using
    Classical.choose_spec inputProgram_exists (Nat.pair r (Nat.pair s c))

noncomputable def inputColumn (r s : Nat) : Program := (inputProgram.column r).column s

theorem inputColumn_primrec : Primrec₂ inputColumn :=
  (Program.column_primrec.comp
    (Program.column_primrec.comp (Primrec.const inputProgram) Primrec.fst) Primrec.snd).to₂

theorem inputColumn_domain (r s c : Nat) : (inputColumn r s).domain c ↔
    r ≤ s ∧ checkCode s c = true ∧ interpretation s c < finiteBase (r + 1) := by
  rw [inputColumn, Program.column_domain, Program.column_domain]
  exact inputProgram_domain r s c

def graphRaw (query : Nat) : Bool :=
  let input := inputTuple query.unpair.1
  BoundedLowering.graph input.1 input.2.1 input.2.2 query.unpair.2

theorem graphRaw_primrec : Primrec graphRaw :=
  BoundedLowering.graph_primrec.comp
    ((inputTuple_primrec.comp (Primrec.fst.comp Primrec.unpair)).pair (Primrec.snd.comp Primrec.unpair))

theorem graphProgram_exists : ∃ p : Program, ∀ query, p.domain query ↔ graphRaw query = true :=
  positiveProgram_exists graphRaw graphRaw_primrec

noncomputable def graphProgram : Program := Classical.choose graphProgram_exists

theorem graphProgram_domain (r s c q : Nat) : graphProgram.domain (Nat.pair (Nat.pair r (Nat.pair s c)) q) ↔
    r ≤ s ∧ checkCode s c = true ∧ interpretation s c < finiteBase (r + 1) ∧
      Canonical.check q = true ∧ unionInterpretation q = interpretation s c := by
  simpa only [graphRaw, inputTuple, Nat.unpair_pair, BoundedLowering.graph_exact] using
    Classical.choose_spec graphProgram_exists (Nat.pair (Nat.pair r (Nat.pair s c)) q)

noncomputable def graphColumn (r s c : Nat) : Program := graphProgram.column (Nat.pair r (Nat.pair s c))

theorem graphColumn_primrec : Primrec (fun p : Nat × (Nat × Nat) => graphColumn p.1 p.2.1 p.2.2) :=
  Program.column_primrec.comp (Primrec.const graphProgram)
    (Primrec₂.natPair.comp Primrec.fst (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem graphColumn_domain (r s c q : Nat) : (graphColumn r s c).domain q ↔
    r ≤ s ∧ checkCode s c = true ∧ interpretation s c < finiteBase (r + 1) ∧
      Canonical.check q = true ∧ unionInterpretation q = interpretation s c := by
  rw [graphColumn, Program.column_domain]
  exact graphProgram_domain r s c q

theorem graphColumn_unique (r s c : Nat) (h : BoundedLowering.checkInput r s c = true) :
    ∃! q, (graphColumn r s c).domain q := by
  have hs := (BoundedLowering.checkInput_exact r s c).mp h
  refine ⟨BoundedLowering.canonicalLower r s c, (graphColumn_domain r s c _).mpr
    ⟨hs.1, hs.2.1, hs.2.2, BoundedLowering.canonicalLower_checked r s c h,
      BoundedLowering.canonicalLower_value r s c h⟩, ?_⟩
  intro q hq
  have ht := (graphColumn_domain r s c q).mp hq
  exact Canonical.check_value_injective _ _ ht.2.2.2.1 (BoundedLowering.canonicalLower_checked r s c h)
    (ht.2.2.2.2.trans (BoundedLowering.canonicalLower_value r s c h).symm)

end Alexander313.HereditaryBoundedLoweringProgram
