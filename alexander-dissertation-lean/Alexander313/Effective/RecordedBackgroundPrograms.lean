import Alexander313.Effective.RecordedFormation

/-!
# Positive recorded-background image compiler

The seven rows are the literal existing `RecordedBackground` table. All
finite policy/nesting checks are computed, and validity/contextual edges are
ordinary executing program inputs, used only through positive bounded
computations. Exact semantic identification retains their exact-domain
hypotheses. No validity inferred from erasure is admitted.
-/

noncomputable section

namespace Alexander313
namespace RecordedBackgroundProgram

open RecordedFormula

abbrev Witness := (Nat × (Nat × Nat)) ×
  ((Head × (Syntax × Syntax)) × (List Nat × (List Frame × SyntacticBackground.Witness)))

abbrev Parameters := ((List Nat × List Nat) × Program) × Program

def defaultWitness : Witness :=
  ((0, (0, 0)), ((.live 0, (.falsum, .falsum)), ([], ([], ((0, 0), (.falsum, .falsum))))))

def formula (a : Nat) (w : Witness) : Syntax :=
  if w.1.1 = 0 then paFormula w.2.2.2.2 else
  if w.1.1 = 1 then close w.2.1.2.1 w.2.2.1 else
  if w.1.1 = 2 then Formula.universalClosure (.know (.indexed a w.1.2.2) w.2.1.2.1) else
  if w.1.1 = 3 then Formula.indexedDeduction a w.1.2.2 w.2.1.2.1 w.2.1.2.2 else
  if w.1.1 = 4 then Formula.indexedIntrospection a w.1.2.1 w.1.2.2 w.2.1.2.1 else
  if w.1.1 = 5 then reflection w.2.1.1 w.2.1.2.1 else
  collapse w.2.2.2.1 w.2.1.1.erase w.1.2.1 w.1.2.2 w.2.1.2.1

theorem formula_primrec : Primrec₂ formula := by
  have hw : Primrec (fun p : Nat × Witness => p.2) := Primrec.snd
  have ht := Primrec.fst.comp (Primrec.fst.comp hw)
  have hμ := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp hw))
  have hν := Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp hw))
  have hbody := Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp hw))
  have hφ := Primrec.fst.comp hbody
  have hψ := Primrec.snd.comp hbody
  have hh := Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp hw))
  have hrest := Primrec.snd.comp (Primrec.snd.comp hw)
  have hL := Primrec.fst.comp hrest
  have hcontext := Primrec.fst.comp (Primrec.snd.comp hrest)
  have hpa := Primrec.snd.comp (Primrec.snd.comp hrest)
  have test (n : Nat) := Primrec.eq.comp ht (Primrec.const n)
  have hknown := universalClosure_primrec.comp
    (know_primrec.comp (RecordedHead.indexed_primrec.comp Primrec.fst hν) hφ)
  have hded := indexedDeduction_primrec.comp ((Primrec.fst.pair hν).pair (hφ.pair hψ))
  have hintro := indexedIntrospection_primrec.comp ((Primrec.fst.pair (hμ.pair hν)).pair hφ)
  have hcollapse := collapse_primrec.comp
    ((hcontext.pair ((RecordedHead.erase_primrec.comp hh).pair (hμ.pair hν))).pair hφ)
  exact (Primrec.ite (test 0) (paFormula_primrec.comp hpa)
    (Primrec.ite (test 1) (close_primrec.comp hφ hL)
      (Primrec.ite (test 2) hknown
        (Primrec.ite (test 3) hded (Primrec.ite (test 4) hintro
          (Primrec.ite (test 5) (reflection_primrec.comp hh hφ) hcollapse)))))).to₂

theorem formula_closed (a : Nat) (w : Witness) : (formula a w).Closed := by
  unfold formula
  split_ifs
  · exact paFormula_closed _
  · exact Formula.close_closed _ _
  all_goals exact Formula.universalClosure_closed _

def branch (p : Parameters) (w : Witness) : Prop :=
  if w.1.1 = 0 then w.2.2.2.2.1.1 ≤ 6 else
  if w.1.1 = 1 ∨ w.1.1 = 2 then p.2.domain (w.2.1.2.1.code RecordedHead.code) else
  if w.1.1 = 3 then True else
  if w.1.1 = 4 then w.1.2.1 < w.1.2.2 else
  if w.1.1 = 5 then True else p.1.2.domain (Nat.pair w.1.2.1 w.1.2.2)

def side (p : Parameters) (a : Nat) (w : Witness) : Prop :=
  (formula a w).RecordedAdmissible p.1.1.1.toFinset p.1.1.2.toFinset ∧ branch p w

def admits (p : Parameters) (a : Nat) (σ : Syntax) : Prop :=
  ∃ w : Witness, side p a w ∧ σ = formula a w

theorem admits_closed {p : Parameters} {a : Nat} {σ : Syntax} (h : admits p a σ) : σ.Closed := by
  obtain ⟨w, _, rfl⟩ := h
  exact formula_closed a w

theorem admits_admissible {p : Parameters} {a : Nat} {σ : Syntax} (h : admits p a σ) :
    σ.RecordedAdmissible p.1.1.1.toFinset p.1.1.2.toFinset := by
  obtain ⟨w, h, rfl⟩ := h
  exact h.1

theorem background_exact (p : Parameters) (R : Nat → Nat → Prop)
    (hedge : ∀ μ ν, p.1.2.domain (Nat.pair μ ν) ↔ R μ ν)
    (hvalid : ∀ φ : Formula Nat, p.2.domain (φ.code id) ↔ Valid φ)
    (a : Nat) (σ : Syntax) :
    admits p a σ ↔ RecordedBackground p.1.1.1.toFinset p.1.1.2.toFinset a R σ := by
  have hv (φ : Syntax) : p.2.domain (φ.code RecordedHead.code) ↔ Valid φ := by
    rw [← encode_code, hvalid, valid_encode]
  constructor
  · rintro ⟨w, ⟨ha, hb⟩, rfl⟩
    by_cases h0 : w.1.1 = 0
    · simp only [formula, if_pos h0] at ha ⊢
      exact .arithmetic (paFormula_pa _ (by simpa [branch, h0] using hb)) ha
    by_cases h1 : w.1.1 = 1
    · simp only [formula, if_neg h0, if_pos h1, close] at ha ⊢
      exact .assigned _ _ ((hv _).mp (by simpa [branch, h0, h1] using hb))
        ((Formula.recordedAdmissible_close _ _ _ _).mp ha)
    by_cases h2 : w.1.1 = 2
    · simp only [formula, if_neg h0, if_neg h1, if_pos h2] at ha ⊢
      exact .own_validity _ _ ((hv _).mp (by simpa [branch, h0, h1, h2] using hb)) ha
    by_cases h3 : w.1.1 = 3
    · simp only [formula, if_neg h0, if_neg h1, if_neg h2, if_pos h3] at ha ⊢
      exact .deduction _ _ _ ha
    by_cases h4 : w.1.1 = 4
    · simp only [formula, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4] at ha ⊢
      exact .introspection _ _ _ (by simpa [branch, h0, h1, h2, h3, h4] using hb) ha
    by_cases h5 : w.1.1 = 5
    · simp only [formula, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
        if_pos h5] at ha ⊢
      exact .reflection _ _ ha
    · simp only [formula, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
        if_neg h5, collapse] at ha ⊢
      exact .contextual _ _ _ _ _
        ((hedge _ _).mp (by simpa [branch, h0, h1, h2, h3, h4, h5] using hb)) ha
  · intro h
    cases h with
    | arithmetic hp ha =>
      obtain ⟨v, ht, hσ⟩ := pa_represents σ hp
      let w : Witness := ((0, (0, 0)), ((.live 0, (.falsum, .falsum)), ([], ([], v))))
      exact ⟨w, by simpa [side, formula, branch, w, ← hσ] using And.intro ha ht,
        by simpa [formula, w] using hσ⟩
    | assigned φ s hvφ ha =>
      obtain ⟨L, hL⟩ := close_represents φ s
      let w : Witness := ((1, (0, 0)), ((.live 0, (φ, .falsum)),
        (L, ([], ((0, 0), (.falsum, .falsum))))))
      refine ⟨w, ⟨?_, ?_⟩, ?_⟩
      · simpa [formula, w, close] using
          (Formula.recordedAdmissible_close _ _ φ (FiniteAssignment.assignment L)).mpr ha
      · simpa [branch, w] using (hv φ).mpr hvφ
      · simpa [formula, w] using hL
    | own_validity ν φ hvφ ha =>
      let w : Witness := ((2, (0, ν)), ((.live 0, (φ, .falsum)),
        ([], ([], ((0, 0), (.falsum, .falsum))))))
      exact ⟨w, ⟨by simpa [formula, w] using ha,
        by simpa [branch, w] using (hv φ).mpr hvφ⟩, rfl⟩
    | deduction ν φ ψ ha =>
      let w : Witness := ((3, (0, ν)), ((.live 0, (φ, ψ)),
        ([], ([], ((0, 0), (.falsum, .falsum))))))
      exact ⟨w, by simpa [side, formula, branch, w] using ha, rfl⟩
    | introspection μ ν φ hμν ha =>
      let w : Witness := ((4, (μ, ν)), ((.live 0, (φ, .falsum)),
        ([], ([], ((0, 0), (.falsum, .falsum))))))
      exact ⟨w, by simpa [side, formula, branch, w] using And.intro ha hμν, rfl⟩
    | reflection b φ ha =>
      let w : Witness := ((5, (0, 0)), ((b, (φ, .falsum)),
        ([], ([], ((0, 0), (.falsum, .falsum))))))
      exact ⟨w, by simpa [side, formula, branch, w] using ha, rfl⟩
    | contextual c b μ ν φ hr ha =>
      obtain ⟨L, hL⟩ := context_represents c
      let w : Witness := ((6, (μ, ν)), ((.live b, (φ, .falsum)),
        ([], (L, ((0, 0), (.falsum, .falsum))))))
      refine ⟨w, ⟨?_, ?_⟩, ?_⟩
      · simpa [formula, w, collapse, RecordedHead.erase, hL] using ha
      · simpa [branch, w] using (hedge μ ν).mpr hr
      · simp [formula, w, collapse, RecordedHead.erase, hL]

def positive (cutoff : Nat) (c : Program) (n : Nat) : Bool :=
  (Nat.Partrec.Code.evaln cutoff c n).isSome

theorem positive_primrec : Primrec (fun p : (Nat × Program) × Nat => positive p.1.1 p.1.2 p.2) :=
  Primrec.option_isSome.comp Nat.Partrec.Code.primrec_evaln

theorem positive_iff (c : Program) (n : Nat) :
    (∃ cutoff, positive cutoff c n = true) ↔ c.domain n := by
  constructor
  · rintro ⟨cutoff, h⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    exact (Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)).1
  · intro h
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
    obtain ⟨cutoff, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    exact ⟨cutoff, by simp [positive, Option.mem_def.mp hk]⟩

def branchCheck (p : Parameters) (w : Witness) (cutoff : Nat) : Bool :=
  if w.1.1 = 0 then decide (w.2.2.2.2.1.1 ≤ 6) else
  if w.1.1 = 1 ∨ w.1.1 = 2 then positive cutoff p.2 (w.2.1.2.1.code RecordedHead.code) else
  if w.1.1 = 3 then true else
  if w.1.1 = 4 then decide (w.1.2.1 < w.1.2.2) else
  if w.1.1 = 5 then true else positive cutoff p.1.2 (Nat.pair w.1.2.1 w.1.2.2)

set_option maxHeartbeats 800000 in
theorem branchCheck_primrec : Primrec (fun p : (Parameters × Witness) × Nat =>
    branchCheck p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Parameters × Witness) × Nat => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hw : Primrec (fun p : (Parameters × Witness) × Nat => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have ht := Primrec.fst.comp (Primrec.fst.comp hw)
  have hμ := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp hw))
  have hν := Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp hw))
  have hφ := code_primrec.comp
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp hw))))
  have hpa := Primrec.fst.comp (Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hw)))))
  have hedge := Primrec.snd.comp (Primrec.fst.comp hp)
  have hvalid := Primrec.snd.comp hp
  have test (n : Nat) := Primrec.eq.comp ht (Primrec.const n)
  have result := Primrec.ite (test 0) (Primrec.nat_le.comp hpa (Primrec.const 6)).decide
    (Primrec.ite ((test 1).or (test 2))
      (positive_primrec.comp ((Primrec.snd.pair hvalid).pair hφ))
      (Primrec.ite (test 3) (Primrec.const true)
        (Primrec.ite (test 4) (Primrec.nat_lt.comp hμ hν).decide
          (Primrec.ite (test 5) (Primrec.const true)
            (positive_primrec.comp ((Primrec.snd.pair hedge).pair (Primrec₂.natPair.comp hμ hν)))))))
  exact result.of_eq (fun _ => rfl)

theorem branchCheck_correct (p : Parameters) (w : Witness) :
    (∃ cutoff, branchCheck p w cutoff = true) ↔ branch p w := by
  unfold branchCheck branch
  split_ifs <;> simp [positive_iff]

def condition (p : Parameters) (a : Nat) (w : Witness) (cutoff : Nat) : Bool :=
  admissibleCode p.1.1 ((formula a w).code RecordedHead.code) && branchCheck p w cutoff

set_option maxHeartbeats 800000 in
theorem condition_primrec : Primrec (fun p : (Parameters × Nat) × (Witness × Nat) =>
    condition p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hp : Primrec (fun p : (Parameters × Nat) × (Witness × Nat) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : (Parameters × Nat) × (Witness × Nat) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : (Parameters × Nat) × (Witness × Nat) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hk : Primrec (fun p : (Parameters × Nat) × (Witness × Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hAE := Primrec.fst.comp (Primrec.fst.comp hp)
  have result := Primrec.and.comp (admissibleCode_primrec.comp hAE (code_primrec.comp (formula_primrec.comp ha hw)))
    (branchCheck_primrec.comp ((hp.pair hw).pair hk))
  exact result.of_eq (fun _ => rfl)

theorem condition_correct (p : Parameters) (a : Nat) (w : Witness) :
    (∃ cutoff, condition p a w cutoff = true) ↔ side p a w := by
  simp only [condition, Bool.and_eq_true, admissibleCode_code, exists_and_left,
    branchCheck_correct, side]

def decodeWitness (n : Nat) : Witness := (Encodable.decode (α := Witness) n).getD defaultWitness
def defaultParameters : Parameters := ((([], []), Nat.Partrec.Code.zero), Nat.Partrec.Code.zero)
def decodeParameters (n : Nat) : Parameters := (Encodable.decode (α := Parameters) n).getD defaultParameters

theorem decodeWitness_primrec : Primrec decodeWitness :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const defaultWitness)
theorem decodeParameters_primrec : Primrec decodeParameters :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const defaultParameters)

@[simp] theorem decodeWitness_encode (w : Witness) : decodeWitness (Encodable.encode w) = w := by
  simp [decodeWitness]
@[simp] theorem decodeParameters_encode (p : Parameters) : decodeParameters (Encodable.encode p) = p := by
  simp only [decodeParameters, Encodable.encodek, Option.getD_some]

def check (key query certificate : Nat) : Bool :=
  let p := decodeParameters key
  let w := decodeWitness certificate.unpair.1
  condition p query.unpair.1 w certificate.unpair.2 &&
    (query.unpair.2 == (formula query.unpair.1 w).code RecordedHead.code)

set_option maxHeartbeats 800000 in
theorem check_primrec : Primrec (fun p : (Nat × Nat) × Nat => check p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (Nat × Nat) × Nat => decodeParameters p.1.1) :=
    decodeParameters_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hq : Primrec (fun p : (Nat × Nat) × Nat => p.1.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)
  have ha := Primrec.fst.comp hq
  have hσ := Primrec.snd.comp hq
  have hc : Primrec (fun p : (Nat × Nat) × Nat => p.2.unpair) :=
    Primrec.unpair.comp Primrec.snd
  have hw := decodeWitness_primrec.comp (Primrec.fst.comp hc)
  have hk := Primrec.snd.comp hc
  have result := Primrec.and.comp (condition_primrec.comp ((hp.pair ha).pair (hw.pair hk)))
    (Primrec.beq.comp hσ (code_primrec.comp (formula_primrec.comp ha hw)))
  exact result.of_eq (fun _ => by simp only [check, Bool.beq_eq_decide_eq])

def evaluation (key query : Nat) : Part Nat :=
  Nat.rfind (fun certificate => Part.some (check key query certificate))

theorem evaluation_partrec : Partrec₂ evaluation :=
  (Partrec.rfind check_primrec.to_comp.partrec.to₂).to₂

theorem evaluation_domain (key query : Nat) :
    (evaluation key query).Dom ↔ ∃ certificate, check key query certificate = true := by
  simp only [evaluation, Nat.rfind_dom, Part.mem_some_iff, Part.some_dom,
    implies_true, and_true, Bool.true_eq]

theorem evaluation_correct (p : Parameters) (a : Nat) (σ : Syntax) :
    (evaluation (Encodable.encode p) (Nat.pair a (σ.code RecordedHead.code))).Dom ↔ admits p a σ := by
  rw [evaluation_domain]
  constructor
  · rintro ⟨t, ht⟩
    let w := decodeWitness t.unpair.1
    have hc : condition p a w t.unpair.2 = true ∧
        σ.code RecordedHead.code = (formula a w).code RecordedHead.code := by
      simpa only [check, Nat.unpair_pair, decodeParameters_encode, Bool.and_eq_true, beq_iff_eq] using ht
    exact ⟨w, (condition_correct p a w).mp ⟨_, hc.1⟩,
      Formula.code_injective RecordedHead.code RecordedHead.code_injective hc.2⟩
  · rintro ⟨w, hs, rfl⟩
    obtain ⟨cutoff, hc⟩ := (condition_correct p a w).mpr hs
    exact ⟨Nat.pair (Encodable.encode w) cutoff, by simp [check, hc]⟩

theorem evaluation_only_sentences (key query : Nat) (h : (evaluation key query).Dom) :
    ∃ a, ∃ σ : Syntax, query = Nat.pair a (σ.code RecordedHead.code) ∧
      σ.Closed ∧ σ.RecordedAdmissible
        (decodeParameters key).1.1.1.toFinset (decodeParameters key).1.1.2.toFinset := by
  obtain ⟨t, ht⟩ := (evaluation_domain key query).mp h
  let w := decodeWitness t.unpair.1
  let σ := formula query.unpair.1 w
  have hc : query.unpair.2 = σ.code RecordedHead.code := beq_iff_eq.mp (Bool.and_eq_true_iff.mp ht).2
  have hs : side (decodeParameters key) query.unpair.1 w :=
    (condition_correct _ _ _).mp ⟨_, (Bool.and_eq_true_iff.mp ht).1⟩
  refine ⟨query.unpair.1, σ, ?_, formula_closed _ _, hs.1⟩
  rw [← hc]
  exact (Nat.pair_unpair query).symm

theorem compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ p a σ, (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔ admits p a σ) ∧
    (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed ∧
        σ.RecordedAdmissible p.1.1.1.toFinset p.1.1.2.toFinset) := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr evaluation_partrec)
  let compiler : Parameters → Program := fun p => Nat.Partrec.Code.curry kernel (Encodable.encode p)
  have heval (p : Parameters) (query : Nat) : (compiler p).eval query =
      evaluation (Encodable.encode p) query := by
    change (Nat.Partrec.Code.curry kernel _).eval query = _
    rw [Nat.Partrec.Code.eval_curry, hkernel]
    simp only [Nat.unpaired, Nat.unpair_pair]
  refine ⟨compiler, Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel) Primrec.encode, ?_, ?_⟩
  · intro p a σ
    change ((compiler p).eval _).Dom ↔ _
    rw [heval]
    exact evaluation_correct p a σ
  · intro p query h
    change ((compiler p).eval query).Dom at h
    rw [heval] at h
    simpa only [decodeParameters_encode] using evaluation_only_sentences _ _ h

end RecordedBackgroundProgram
end Alexander313
