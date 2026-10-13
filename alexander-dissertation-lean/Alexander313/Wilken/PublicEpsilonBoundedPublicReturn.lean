import Alexander313.Wilken.PublicEpsilonNativeContextSupport

/-!
# Executing a genuine public return at every canonical epsilon reference

The finite source dictionary selects the whole original RAW LOW return at
base points and the actual bounded SAME-value return in both proper cases.
The selected proper endpoint remains the ORIGINAL source alpha-plus.
Every original input below its base derives that endpoint bound, including
every admitted parameter. This is a genuine return callback; it does not
replace an arbitrary-base mu with a fixed-source operation. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicEpsilonSourceDictionary.Return

open PublicEpsilonSourceDictionary

/-- The whole base-point LOW interval or the actual selected proper bound. -/
noncomputable def endpoint (q : Nat) : Ordinal.{0} :=
  if basePoint q = true then omegaSequence (NativeContext.base q) 1
  else if level q = 0 then SourceOneIota.Enclosure.sourceAlphaPlus (sourceRootCode q)
  else NativeContext.Iota.AlphaPlus.sourceValue (sourceIndex q) (positiveRootCode q)

def inputCheck (q c : Nat) : Bool := PublicEpsilonSourceDictionary.inputCheck q &&
  cond (basePoint q) (NativeContext.lowCheckCode q c)
    (cond (level q == 0) (SourceOneIota.BoundedPublicReturn.inputCheck (sourceRootCode q) c)
      (NativeContext.BoundedPublicReturn.inputCheck (sourceIndex q) (positiveRootCode q) c))

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp (PublicEpsilonSourceDictionary.inputCheck_primrec.comp Primrec.fst)
    ((basePoint_primrec.comp Primrec.fst).cond NativeContext.lowCheckCode_primrec
      ((Primrec.beq.comp (level_primrec.comp Primrec.fst) (Primrec.const 0)).cond
        (SourceOneIota.BoundedPublicReturn.inputCheck_primrec.comp
          (sourceRootCode_primrec.comp Primrec.fst) Primrec.snd)
        (NativeContext.BoundedPublicReturn.inputCheck_primrec.comp
          (((sourceIndex_primrec.comp Primrec.fst).pair
            (positiveRootCode_primrec.comp Primrec.fst)).pair Primrec.snd))))).to₂

theorem inputCheck_exact (q c : Nat) : inputCheck q c = true ↔
    PublicEpsilonSourceDictionary.inputCheck q = true ∧
      NativeContext.lowCheckCode q c = true ∧ NativeContext.interpretation q c < endpoint q := by
  by_cases hq : PublicEpsilonSourceDictionary.inputCheck q = true
  · cases hb : basePoint q with
    | true =>
      simp only [inputCheck, hq, hb, Bool.cond_true, Bool.true_and,
        endpoint, if_pos rfl, true_and]
      exact ⟨fun hc => ⟨hc, (NativeContext.HeightBoundary.input_spec q c hc).2.2⟩,
        fun hc => hc.1⟩
    | false =>
      cases hl : level q with
      | zero =>
        simpa only [inputCheck, hq, hb, hl, beq_self_eq_true, Bool.cond_false,
          Bool.cond_true, Bool.true_and, endpoint, Bool.false_eq_true, if_false, if_pos rfl, true_and]
          using source_one_return_guard q c hq hl
      | succ s =>
        have hi : sourceIndex q = s := by unfold sourceIndex; omega
        have hz : (s + 1 == 0) = false := by simp
        have hn : s + 1 ≠ 0 := by omega
        simpa only [inputCheck, hq, hb, hl, hi, hz, Bool.cond_false, Bool.true_and,
          endpoint, Bool.false_eq_true, if_false, hn, true_and]
          using positive_return_guard q s c hq hl hb
  · have hf : PublicEpsilonSourceDictionary.inputCheck q = false :=
      Bool.eq_false_of_not_eq_true hq
    simp only [inputCheck, hf, Bool.false_and, Bool.false_eq_true, false_and]

def publicCode (q c : Nat) : Nat := cond (inputCheck q c)
  (cond (basePoint q) (base_point_publicCode q c)
    (cond (level q == 0) (SourceOneIota.BoundedPublicReturn.publicCode (sourceRootCode q) c)
      (NativeContext.BoundedPublicReturn.publicCode (sourceIndex q) (positiveRootCode q) c))) 0

theorem publicCode_primrec : Primrec₂ publicCode :=
  (inputCheck_primrec.cond
    ((basePoint_primrec.comp Primrec.fst).cond base_point_publicCode_primrec
      ((Primrec.beq.comp (level_primrec.comp Primrec.fst) (Primrec.const 0)).cond
        (SourceOneIota.BoundedPublicReturn.publicCode_primrec.comp
          (sourceRootCode_primrec.comp Primrec.fst) Primrec.snd)
        (NativeContext.BoundedPublicReturn.publicCode_primrec.comp
          (((sourceIndex_primrec.comp Primrec.fst).pair
            (positiveRootCode_primrec.comp Primrec.fst)).pair Primrec.snd))))
    (Primrec.const 0)).to₂

theorem publicCode_spec (q c : Nat) (hc : inputCheck q c = true) :
    Canonical.check (publicCode q c) = true ∧
      unionInterpretation (publicCode q c) = NativeContext.interpretation q c := by
  have hs := (inputCheck_exact q c).mp hc
  cases hb : basePoint q with
  | true =>
    simpa only [publicCode, hc, hb, Bool.cond_true] using
      base_point_publicCode_spec q c hs.1 hb hs.2.1
  | false =>
    cases hl : level q with
    | zero =>
      have he : NativeContext.interpretation q c <
          SourceOneIota.Enclosure.sourceAlphaPlus (sourceRootCode q) := by
        simpa only [endpoint, hb, Bool.false_eq_true, if_false, hl, if_pos rfl] using hs.2.2
      simpa only [publicCode, hc, hb, hl, beq_self_eq_true, Bool.cond_true, Bool.cond_false]
        using source_one_return_spec q c hs.1 hl hs.2.1 he
    | succ s =>
      have hi : sourceIndex q = s := by unfold sourceIndex; omega
      have hz : (s + 1 == 0) = false := by simp
      have hn : s + 1 ≠ 0 := by omega
      have he : NativeContext.interpretation q c <
          NativeContext.Iota.AlphaPlus.sourceValue s (positiveRootCode q) := by
        simpa only [endpoint, hb, Bool.false_eq_true, if_false, hl, hn, hi] using hs.2.2
      simpa only [publicCode, hc, hb, hl, hi, hz, Bool.cond_true, Bool.cond_false]
        using positive_return_spec q s c hs.1 hl hb hs.2.1 he

theorem publicCode_invalid (q c : Nat) (hc : inputCheck q c = false) : publicCode q c = 0 := by
  simp only [publicCode, hc, Bool.cond_false]

/-- The genuine original source-one successor collapse bounds its root. -/
theorem source_one_root_lt_endpoint (a : Nat) (ha : SourceOneIota.rootCheck a = true) :
    interpretation 0 a < SourceOneIota.Enclosure.sourceAlphaPlus a := by
  obtain ⟨t, he, ht, hn, hh⟩ := (SourceOneIota.rootCheck_exact a).mp ha
  have hc := SourceOneIota.OrderSupport.argument_checked 0 t ht
  have hA : GlobalNotation (finiteBase 0) 1
      (interpretation 0 (SourceOneIota.Lambda.argumentCode a)) := by
    simpa only [SourceOneIota.OmegaQuotient.argumentCode, he,
      Localization.argumentCode_theta, interpretation_code] using
      SourceDecomposition.checked_all_levels 0 1 t hc
  have hsort : interpretation 0 (SourceOneIota.Lambda.argumentCode a) < omegaSequence (finiteBase 0) 2 := by
    simpa only [SourceOneIota.OmegaQuotient.argumentCode, he,
      Localization.argumentCode_theta, interpretation_code] using SourceFixedPoint.checked_theta_sort 0 0 t ht
  have hroot : interpretation 0 a = globalCollapse (finiteBase 0) 0
      (interpretation 0 (SourceOneIota.Lambda.argumentCode a)) := by
    simp only [he, SourceOneIota.OmegaQuotient.argumentCode,
      Localization.argumentCode_theta, interpretation_code]
    rfl
  rw [hroot]
  exact SourceCollapseSuccessors.global_collapse_lt_successor (finiteBase 0) (finiteBase_pos 0) 0
    ⟨interpretation 0 (SourceOneIota.Lambda.argumentCode a), hA⟩ hsort

theorem base_lt_endpoint (q : Nat) (hq : PublicEpsilonSourceDictionary.inputCheck q = true) :
    NativeContext.base q < endpoint q := by
  cases hb : basePoint q with
  | true =>
    simpa only [endpoint, hb, if_pos rfl] using omegaSequence_step (NativeContext.base q) 0
  | false =>
    cases hl : level q with
    | zero =>
      have hs := source_one_spec q hq hl
      have he := source_one_root_lt_endpoint (sourceRootCode q) hs.1
      simpa only [endpoint, hb, Bool.false_eq_true, if_false, hl, if_pos rfl, hs.2.1] using he
    | succ s =>
      have hs := positive_spec q s hq hl hb
      obtain ⟨t, ht, hc, hn, hh⟩ := (NativeContext.Iota.rootCheck_exact s _).mp hs.2.1
      have hi := (NativeContext.SourceZeta.inputCheck_exact s _).mpr ⟨t, ht, hc, hn⟩
      have he := NativeContext.Iota.AlphaPlus.root_lt_sourceValue s (positiveRootCode q) hi
      have hz : s + 1 ≠ 0 := by omega
      simpa only [endpoint, hb, Bool.false_eq_true, if_false, hl, hz, hs.1, hs.2.2.1] using he

/-- Every ORIGINAL raw LOW input below q derives the return caller. -/
theorem below_base_input (q c : Nat) (hq : PublicEpsilonSourceDictionary.inputCheck q = true)
    (hc : NativeContext.lowCheckCode q c = true)
    (hb : NativeContext.interpretation q c < NativeContext.base q) : inputCheck q c = true :=
  (inputCheck_exact q c).mpr ⟨hq, hc, hb.trans (base_lt_endpoint q hq)⟩

theorem below_base_public_spec (q c : Nat) (hq : PublicEpsilonSourceDictionary.inputCheck q = true)
    (hc : NativeContext.lowCheckCode q c = true)
    (hb : NativeContext.interpretation q c < NativeContext.base q) :
    Canonical.check (publicCode q c) = true ∧
      unionInterpretation (publicCode q c) = NativeContext.interpretation q c :=
  publicCode_spec q c (below_base_input q c hq hc hb)

/-- Original parameter admission itself supplies the full genuine caller. -/
theorem parameter_public_spec (q p : Nat) (hq : PublicEpsilonSourceDictionary.inputCheck q = true)
    (hp : NativeContext.check q (.parameter p) = true) :
    Canonical.check (publicCode q (.parameter p : RelativeTerm Nat).code) = true ∧
      unionInterpretation (publicCode q (.parameter p : RelativeTerm Nat).code) = NativeContext.parameters p := by
  have hl : NativeContext.lowCheckCode q (.parameter p : RelativeTerm Nat).code = true := by
    simp only [NativeContext.lowCheckCode_code, NativeContext.lowCheck, hp,
      RelativeTerm.outerSort, decide_true, Bool.true_and]
  have hb : NativeContext.parameters p < NativeContext.base q :=
    (NativeContext.checked_parameters q (.parameter p) hp p (by simp [RelativeTerm.parameters])).2
  have hv : NativeContext.interpretation q (.parameter p : RelativeTerm Nat).code < NativeContext.base q := by
    simpa only [NativeContext.interpretation_code, NativeContext.denote, RelativeTerm.eval] using hb
  simpa only [NativeContext.interpretation_code, NativeContext.denote, RelativeTerm.eval] using
    below_base_public_spec q (.parameter p : RelativeTerm Nat).code hq hl hv

def graphCheck (q c out : Nat) : Bool := inputCheck q c && (publicCode q c == out)

theorem graphCheck_primrec : Primrec (fun p : (Nat × Nat) × Nat => graphCheck p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (inputCheck_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
    (Primrec.beq.comp (publicCode_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)) Primrec.snd)

theorem graphCheck_exact (q c out : Nat) : graphCheck q c out = true ↔
    inputCheck q c = true ∧ publicCode q c = out := by
  simp only [graphCheck, Bool.and_eq_true, beq_iff_eq]

def execute (q c : Nat) : Part Nat := cond (inputCheck q c) (Part.some (publicCode q c)) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp publicCode_primrec.to_comp.partrec Partrec.none).to₂

theorem execute_graph (q c out : Nat) : out ∈ execute q c ↔
    inputCheck q c = true ∧ publicCode q c = out := by
  cases h : inputCheck q c <;> simp [execute, h, eq_comm]

theorem graphCheck_execution (q c out : Nat) : graphCheck q c out = true ↔ out ∈ execute q c := by
  rw [graphCheck_exact, execute_graph]

theorem execute_domain (q c : Nat) : (execute q c).Dom ↔ inputCheck q c = true := by
  cases h : inputCheck q c <;> simp [execute, h]

theorem execute_spec (q c out : Nat) (ho : out ∈ execute q c) :
    inputCheck q c = true ∧ Canonical.check out = true ∧
      unionInterpretation out = NativeContext.interpretation q c := by
  obtain ⟨hc, rfl⟩ := (execute_graph q c out).mp ho
  exact ⟨hc, publicCode_spec q c hc⟩

theorem publicCode_value_invariant (q c d : Nat) (hc : inputCheck q c = true)
    (hd : inputCheck q d = true) (he : NativeContext.interpretation q c = NativeContext.interpretation q d) :
    publicCode q c = publicCode q d := by
  have hs := publicCode_spec q c hc
  have ht := publicCode_spec q d hd
  exact Canonical.check_value_injective _ _ hs.1 ht.1 (hs.2.trans (he.trans ht.2.symm))

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicEpsilonSourceDictionary.Return
