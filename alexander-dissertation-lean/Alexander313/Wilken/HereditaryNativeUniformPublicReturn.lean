import Alexander313.Wilken.HereditaryNativeUniformPublicReturnSupport
import Alexander313.Wilken.SourceOneUnboundedPublicReturn

/-!
# Uniform finite SAME-value public return at every coded epsilon

The actual canonical epsilon dictionary selects a basepoint, a proper
original source-one root or a proper positive original-source root. Each
branch executes its concrete WHOLE RAW LOW producer. Canonicalizing the
original base spelling preserves its actual input check and value. No
selected successor endpoint, Normal premise, hidden-call or return oracle.
The complete numerical graph includes output zero. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.UniformPublicReturn

theorem source_one_return_guard (q c : Nat)
    (hq : PublicEpsilonSourceDictionary.inputCheck q = true)
    (hl : PublicEpsilonSourceDictionary.level q = 0) :
    SourceOneIota.UnboundedPublicReturn.inputCheck
      (PublicEpsilonSourceDictionary.sourceRootCode q) c = true ↔ lowCheckCode q c = true := by
  have hs := PublicEpsilonSourceDictionary.source_one_spec q hq hl
  simp only [SourceOneIota.UnboundedPublicReturn.inputCheck_exact, hs.1, ← hs.2.2, true_and]

theorem source_one_return_spec (q c : Nat)
    (hq : PublicEpsilonSourceDictionary.inputCheck q = true)
    (hl : PublicEpsilonSourceDictionary.level q = 0) (hc : lowCheckCode q c = true) :
    Canonical.check (SourceOneIota.UnboundedPublicReturn.publicCode
      (PublicEpsilonSourceDictionary.sourceRootCode q) c) = true ∧
      unionInterpretation (SourceOneIota.UnboundedPublicReturn.publicCode
        (PublicEpsilonSourceDictionary.sourceRootCode q) c) = interpretation q c := by
  have hs := SourceOneIota.UnboundedPublicReturn.publicCode_spec _ c
    ((source_one_return_guard q c hq hl).mpr hc)
  simpa only [← (PublicEpsilonSourceDictionary.source_one_spec q hq hl).2.2] using hs

def inputCheck (q c : Nat) : Bool := baseCheck q && lowCheckCode q c

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp (baseCheck_primrec.comp Primrec.fst) lowCheckCode_primrec).to₂

/-- The guard is precisely original RAW LOW admission at any actual
coded epsilon, including every noncanonical admitted base spelling. -/
theorem inputCheck_exact (q c : Nat) : inputCheck q c = true ↔ lowCheckCode q c = true := by
  constructor
  · intro hi; exact (Bool.and_eq_true.mp hi).2
  · intro hc
    have hq := (Bool.and_eq_true.mp (Bool.and_eq_true.mp hc).1).1
    exact Bool.and_eq_true.mpr ⟨hq, hc⟩

def publicCode (q c : Nat) : Nat :=
  let v := canonicalBase q
  cond (inputCheck q c)
    (cond (PublicEpsilonSourceDictionary.basePoint v)
      (PublicEpsilonSourceDictionary.base_point_publicCode v c)
      (cond (PublicEpsilonSourceDictionary.level v == 0)
        (SourceOneIota.UnboundedPublicReturn.publicCode (PublicEpsilonSourceDictionary.sourceRootCode v) c)
        (UnboundedPublicReturn.publicCode (PublicEpsilonSourceDictionary.sourceIndex v)
          (PublicEpsilonSourceDictionary.positiveRootCode v) c))) 0

theorem publicCode_primrec : Primrec₂ publicCode := by
  have hv := canonicalBase_primrec.comp Primrec.fst
  have hb := PublicEpsilonSourceDictionary.base_point_publicCode_primrec.comp hv Primrec.snd
  have hz := SourceOneIota.UnboundedPublicReturn.publicCode_primrec.comp
    (PublicEpsilonSourceDictionary.sourceRootCode_primrec.comp hv) Primrec.snd
  have hp := UnboundedPublicReturn.publicCode_primrec.comp
    (((PublicEpsilonSourceDictionary.sourceIndex_primrec.comp hv).pair
      (PublicEpsilonSourceDictionary.positiveRootCode_primrec.comp hv)).pair Primrec.snd)
  exact (inputCheck_primrec.cond
    ((PublicEpsilonSourceDictionary.basePoint_primrec.comp hv).cond hb
      ((Primrec.beq.comp (PublicEpsilonSourceDictionary.level_primrec.comp hv)
        (Primrec.const 0)).cond hz hp)) (Primrec.const 0)).to₂

/-- The concrete three original-source branches return the SAME actual
canonical public value on the WHOLE native coded-epsilon RAW LOW domain. -/
theorem publicCode_spec (q c : Nat) (hi : inputCheck q c = true) :
    Canonical.check (publicCode q c) = true ∧ unionInterpretation (publicCode q c) = interpretation q c := by
  have hc := (inputCheck_exact q c).mp hi
  have hq := (Bool.and_eq_true.mp (Bool.and_eq_true.mp hc).1).1
  let v := canonicalBase q
  have hd := canonicalBase_dictionary q hq
  have hv : lowCheckCode v c = true := (canonicalBase_lowCheck q c hq).trans hc
  have value_eq := canonicalBase_interpretation q c hq
  cases hb : PublicEpsilonSourceDictionary.basePoint v with
  | true =>
    have hs := PublicEpsilonSourceDictionary.base_point_publicCode_spec v c hd hb hv
    simpa only [publicCode, hi, hb, Bool.cond_true] using And.intro hs.1 (hs.2.trans value_eq)
  | false =>
    cases hl : PublicEpsilonSourceDictionary.level v with
    | zero =>
      have hs := source_one_return_spec v c hd hl hv
      simpa only [publicCode, hi, hb, hl, beq_self_eq_true, Bool.cond_true, Bool.cond_false] using
        And.intro hs.1 (hs.2.trans value_eq)
    | succ s =>
      have hs := positive_return_spec v s c hd hl hb hv
      have hindex := (PublicEpsilonSourceDictionary.positive_spec v s hd hl hb).1
      have hn : (s + 1 == 0) = false := by simp
      simpa only [publicCode, hi, hb, hl, hn, hindex, Bool.cond_true, Bool.cond_false] using
        And.intro hs.1 (hs.2.trans value_eq)

theorem publicCode_rejected (q c : Nat) (hi : inputCheck q c = false) : publicCode q c = 0 := by
  simp only [publicCode, hi, Bool.cond_false]

theorem publicCode_value_invariant (q v c d : Nat) (hc : inputCheck q c = true)
    (hd : inputCheck v d = true) (he : interpretation q c = interpretation v d) :
    publicCode q c = publicCode v d :=
  Canonical.check_value_injective _ _ (publicCode_spec q c hc).1 (publicCode_spec v d hd).1
    ((publicCode_spec q c hc).2.trans (he.trans (publicCode_spec v d hd).2.symm))

theorem publicCode_same_base (q v c : Nat) (hq : baseCheck q = true)
    (hv : baseCheck v = true) (he : base q = base v) (hc : lowCheckCode q c = true) :
    publicCode q c = publicCode v c := by
  have ht : lowCheckCode v c = true := (lowCheckCode_invariant q v c hq hv he).symm.trans hc
  exact publicCode_value_invariant q v c c ((inputCheck_exact q c).mpr hc)
    ((inputCheck_exact v c).mpr ht) (interpretation_invariant q v c he)

def execute (q c : Nat) : Part Nat := cond (inputCheck q c) (Part.some (publicCode q c)) Part.none

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.cond inputCheck_primrec.to_comp publicCode_primrec.to_comp.partrec Partrec.none).to₂

theorem execute_domain (q c : Nat) : (execute q c).Dom ↔ lowCheckCode q c = true := by
  cases hi : inputCheck q c <;> simp [execute, hi, ← inputCheck_exact]

theorem execute_graph (q c out : Nat) : out ∈ execute q c ↔
    lowCheckCode q c = true ∧ out = publicCode q c := by
  cases hi : inputCheck q c <;> simp [execute, hi, ← inputCheck_exact]

theorem execute_spec (q c out : Nat) (ho : out ∈ execute q c) :
    Canonical.check out = true ∧ unionInterpretation out = interpretation q c := by
  obtain ⟨hc, rfl⟩ := (execute_graph q c out).mp ho
  exact publicCode_spec q c ((inputCheck_exact q c).mpr hc)

def graphBool (q c out : Nat) : Bool := inputCheck q c && (out == publicCode q c)

theorem graphBool_primrec : Primrec
    (fun p : (Nat × Nat) × Nat => graphBool p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (Primrec.comp inputCheck_primrec Primrec.fst)
    (Primrec.beq.comp Primrec.snd (Primrec.comp publicCode_primrec Primrec.fst))

theorem graphBool_exact (q c out : Nat) : graphBool q c out = true ↔ out ∈ execute q c := by
  rw [execute_graph]
  simp only [graphBool, Bool.and_eq_true, beq_iff_eq, inputCheck_exact]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.UniformPublicReturn
