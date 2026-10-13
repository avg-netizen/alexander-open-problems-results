import Alexander313.Effective.RecordedPrefixPrograms

/-!
# Uniform positive images of actual recorded syntax

This is an ordinary compiler construction for a primitive-recursive formatter
and Boolean certificate checker. Concrete applications supply and prove those
two algorithms. The numerical query must equal the formatter's literal output
code; a total default decoder therefore cannot introduce invalid syntax.
This lemma assumes no semantic validity, genericity or ordinal effectivity.
-/

noncomputable section

namespace Alexander313.RecordedPositiveImage

open RecordedFormula

variable {Data Witness : Type} [Primcodable Data] [Primcodable Witness]

def decode (default : Data) (n : Nat) : Data := (Encodable.decode (α := Data) n).getD default

theorem decode_primrec (default : Data) : Primrec (decode default) :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const default)

@[simp] theorem decode_encode (default : Data) (d : Data) :
    decode default (Encodable.encode d) = d := by simp [decode]

def image (formatter : Data → Nat → Witness → Syntax)
    (condition : Data → Nat → Witness → Bool) (d : Data) (a : Nat) (σ : Syntax) : Prop :=
  ∃ w, condition d a w = true ∧ σ = formatter d a w

def check (defaultData : Data) (defaultWitness : Witness)
    (formatter : Data → Nat → Witness → Syntax)
    (condition : Data → Nat → Witness → Bool) (key query certificate : Nat) : Bool :=
  let d := decode defaultData key
  let w := decode defaultWitness certificate
  condition d query.unpair.1 w &&
    (query.unpair.2 == (formatter d query.unpair.1 w).code RecordedHead.code)

theorem check_primrec (defaultData : Data) (defaultWitness : Witness)
    (formatter : Data → Nat → Witness → Syntax)
    (condition : Data → Nat → Witness → Bool)
    (hformatter : Primrec (fun p : (Data × Nat) × Witness => formatter p.1.1 p.1.2 p.2))
    (hcondition : Primrec (fun p : (Data × Nat) × Witness => condition p.1.1 p.1.2 p.2)) :
    Primrec (fun p : (Nat × Nat) × Nat =>
      check defaultData defaultWitness formatter condition p.1.1 p.1.2 p.2) := by
  have hd : Primrec (fun p : (Nat × Nat) × Nat => decode defaultData p.1.1) := (decode_primrec defaultData).comp (Primrec.fst.comp Primrec.fst)
  have hquery : Primrec (fun p : (Nat × Nat) × Nat => p.1.2.unpair) := Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)
  have ha := Primrec.fst.comp hquery
  have hcode := Primrec.snd.comp hquery
  have hw : Primrec (fun p : (Nat × Nat) × Nat => decode defaultWitness p.2) := (decode_primrec defaultWitness).comp Primrec.snd
  have hinput := (hd.pair ha).pair hw
  exact Primrec.and.comp (hcondition.comp hinput)
    (Primrec.beq.comp hcode (code_primrec.comp (hformatter.comp hinput)))

def evaluation (defaultData : Data) (defaultWitness : Witness)
    (formatter : Data → Nat → Witness → Syntax)
    (condition : Data → Nat → Witness → Bool) (key query : Nat) : Part Nat :=
  Nat.rfind (fun certificate =>
    Part.some (check defaultData defaultWitness formatter condition key query certificate))

theorem evaluation_partrec (defaultData : Data) (defaultWitness : Witness)
    (formatter : Data → Nat → Witness → Syntax)
    (condition : Data → Nat → Witness → Bool)
    (hformatter : Primrec (fun p : (Data × Nat) × Witness => formatter p.1.1 p.1.2 p.2))
    (hcondition : Primrec (fun p : (Data × Nat) × Witness => condition p.1.1 p.1.2 p.2)) :
    Partrec₂ (evaluation defaultData defaultWitness formatter condition) :=
  (Partrec.rfind (check_primrec defaultData defaultWitness formatter condition
    hformatter hcondition).to_comp.partrec.to₂).to₂

theorem evaluation_domain (defaultData : Data) (defaultWitness : Witness)
    (formatter : Data → Nat → Witness → Syntax)
    (condition : Data → Nat → Witness → Bool) (key query : Nat) :
    (evaluation defaultData defaultWitness formatter condition key query).Dom ↔
      ∃ certificate, check defaultData defaultWitness formatter condition key query certificate = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff,
    Part.some_dom, implies_true, and_true, Bool.true_eq]

theorem evaluation_correct (defaultData : Data) (defaultWitness : Witness)
    (formatter : Data → Nat → Witness → Syntax)
    (condition : Data → Nat → Witness → Bool) (d : Data) (a : Nat) (σ : Syntax) :
    (evaluation defaultData defaultWitness formatter condition (Encodable.encode d)
      (Nat.pair a (σ.code RecordedHead.code))).Dom ↔ image formatter condition d a σ := by
  rw [evaluation_domain]
  constructor
  · rintro ⟨certificate, h⟩
    let w := decode defaultWitness certificate
    have hc : condition d a w = true ∧
        σ.code RecordedHead.code = (formatter d a w).code RecordedHead.code := by
      simpa only [check, Nat.unpair_pair, decode_encode, Bool.and_eq_true, beq_iff_eq] using h
    exact ⟨w, hc.1, Formula.code_injective RecordedHead.code RecordedHead.code_injective hc.2⟩
  · rintro ⟨w, hc, rfl⟩
    exact ⟨Encodable.encode w, by simp [check, hc]⟩

/-- Every raw accepted query is exactly an actually formatted typed formula,
    accompanied by the actual successful certificate condition. -/
theorem evaluation_only_images (defaultData : Data) (defaultWitness : Witness)
    (formatter : Data → Nat → Witness → Syntax)
    (condition : Data → Nat → Witness → Bool) (key query : Nat)
    (h : (evaluation defaultData defaultWitness formatter condition key query).Dom) :
    ∃ a, ∃ σ : Syntax, query = Nat.pair a (σ.code RecordedHead.code) ∧
      image formatter condition (decode defaultData key) a σ := by
  obtain ⟨certificate, hc⟩ := (evaluation_domain _ _ _ _ _ _).mp h
  let d := decode defaultData key
  let w := decode defaultWitness certificate
  let σ := formatter d query.unpair.1 w
  have he : query.unpair.2 = σ.code RecordedHead.code :=
    beq_iff_eq.mp (Bool.and_eq_true_iff.mp hc).2
  refine ⟨query.unpair.1, σ, ?_, w, (Bool.and_eq_true_iff.mp hc).1, rfl⟩
  rw [← he]
  exact (Nat.pair_unpair query).symm

theorem compiler_exists (defaultData : Data) (defaultWitness : Witness)
    (formatter : Data → Nat → Witness → Syntax)
    (condition : Data → Nat → Witness → Bool)
    (hformatter : Primrec (fun p : (Data × Nat) × Witness => formatter p.1.1 p.1.2 p.2))
    (hcondition : Primrec (fun p : (Data × Nat) × Witness => condition p.1.1 p.1.2 p.2)) :
    ∃ compiler : Data → Program, Primrec compiler ∧
      (∀ d a σ, (compiler d).domain (Nat.pair a (σ.code RecordedHead.code)) ↔
        image formatter condition d a σ) ∧
      (∀ d query, (compiler d).domain query → ∃ a, ∃ σ : Syntax,
        query = Nat.pair a (σ.code RecordedHead.code) ∧ image formatter condition d a σ) := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr (evaluation_partrec defaultData defaultWitness formatter condition
      hformatter hcondition))
  let compiler : Data → Program := fun d => Nat.Partrec.Code.curry kernel (Encodable.encode d)
  have heval (d : Data) (query : Nat) : (compiler d).eval query =
      evaluation defaultData defaultWitness formatter condition (Encodable.encode d) query := by
    change (Nat.Partrec.Code.curry kernel _).eval query = _
    rw [Nat.Partrec.Code.eval_curry, hkernel]
    simp only [Nat.unpaired, Nat.unpair_pair]
  refine ⟨compiler, Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel) Primrec.encode, ?_, ?_⟩
  · intro d a σ
    change ((compiler d).eval _).Dom ↔ _
    rw [heval]
    exact evaluation_correct _ _ _ _ _ _ _
  · intro d query h
    change ((compiler d).eval query).Dom at h
    rw [heval] at h
    simpa only [decode_encode] using evaluation_only_images _ _ _ _ _ _ h

end Alexander313.RecordedPositiveImage
