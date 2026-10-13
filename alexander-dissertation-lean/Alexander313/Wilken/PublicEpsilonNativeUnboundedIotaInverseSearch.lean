import Alexander313.Wilken.PublicEpsilonNativeUnboundedIotaInverse
import Alexander313.Wilken.HereditaryNativeNormalizationPrimitive
import Mathlib.Computability.Partrec

/-!
# Actual terminating finite inverse search on the whole original domain

The executing predicate tests an ORIGINAL admitted Normal restricted source
code and genuine raw target equality to its literal iota output. Complete
semantic image supplies a witness for every original raw target query.
The actual Nat.rfind therefore terminates without an endpoint or supplied
representative. Invalid queries have an explicit zero witness. Its get
defines a TOTAL computable finite inverse code, with complete executing
graph including zero. The source choice used to prove existence is not
asserted computable or primitive recursive. No parameter provenance or
numerical spelling roundtrip is inferred from semantic equality. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Inverse

abbrev Query := Context × Nat

def inverseInput (q root c : Nat) : Bool :=
  rootCheck q root && checkCode (betaCode q root) c

theorem inverseInput_primrec : Primrec
    (fun p : Query => inverseInput p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (Primrec.comp rootCheck_primrec Primrec.fst)
    (checkCode_primrec.comp (Primrec.comp betaCode_primrec Primrec.fst) Primrec.snd)

theorem inverseInput_exact (q root c : Nat) : inverseInput q root c = true ↔
    rootCheck q root = true ∧ checkCode (betaCode q root) c = true := Bool.and_eq_true

def candidate (q root c d : Nat) : Bool := inputCheck q root d &&
  Normalization.equalRawCode (betaCode q root) (literalCode q root d) c

theorem candidate_primrec : Primrec₂
    (fun p : Query => candidate p.1.1 p.1.2 p.2) := by
  have hctx : Primrec (fun p : Query × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hβ : Primrec (fun p : Query × Nat => betaCode p.1.1.1 p.1.1.2) :=
    Primrec.comp betaCode_primrec hctx
  have hc : Primrec (fun p : Query × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have hd : Primrec (fun p : Query × Nat => literalCode p.1.1.1 p.1.1.2 p.2) :=
    literalCode_primrec.comp hctx Primrec.snd
  exact (Primrec.and.comp (inputCheck_primrec.comp hctx Primrec.snd)
    (Normalization.Effective.equalRawCode_primrec.comp (hβ.pair (hd.pair hc)))).to₂

theorem candidate_exact (q root c d : Nat) : candidate q root c d = true ↔
    inputCheck q root d = true ∧ checkCode (betaCode q root) c = true ∧
      interpretation (betaCode q root) (literalCode q root d) = interpretation (betaCode q root) c := by
  constructor
  · intro h
    have hs := Bool.and_eq_true.mp h
    have hv := (Normalization.equalRawCode_exact _ _ _).mp hs.2
    exact ⟨hs.1, hv.2.1, hv.2.2⟩
  · rintro ⟨hd, hc, hv⟩
    exact Bool.and_eq_true.mpr ⟨hd, (Normalization.equalRawCode_exact _ _ _).mpr
      ⟨literalCode_checked q root d hd, hc, hv⟩⟩

/-- Real original coverage and the constructed semantic lift prove an
actual finite recognized candidate for EVERY original raw target code. -/
theorem candidate_exists (q root c : Nat) (hi : inverseInput q root c = true) :
    ∃ d, candidate q root c d = true := by
  obtain ⟨ha, hc⟩ := (inverseInput_exact q root c).mp hi
  have ht := Arithmetic.raw_checked (betaCode q root) c hc
  have hs := inverse_spec q root ha (ThetaCourse.rawTree c) ht
  have hcall := inverse_iota_caller q root ha (ThetaCourse.rawTree c) ht
  refine ⟨(inverse q root (ThetaCourse.rawTree c)).code,
    (candidate_exact q root c _).mpr ⟨hcall, hc, ?_⟩⟩
  rw [literalCode_code q root ha _ hs.1 hs.2.1 hs.2.2.1, interpretation_code]
  exact hs.2.2.2.trans (Arithmetic.raw_value (betaCode q root) c hc)

def searchTest (p : Query) (d : Nat) : Bool :=
  cond (inverseInput p.1.1 p.1.2 p.2) (candidate p.1.1 p.1.2 p.2 d) (d == 0)

theorem searchTest_primrec : Primrec₂ searchTest :=
  ((inverseInput_primrec.comp Primrec.fst).cond candidate_primrec
    (Primrec.beq.comp Primrec.snd (Primrec.const 0))).to₂

theorem searchTest_exists (p : Query) : ∃ d, searchTest p d = true := by
  cases hi : inverseInput p.1.1 p.1.2 p.2 with
  | false => exact ⟨0, by simp only [searchTest, hi, Bool.cond_false, beq_self_eq_true]⟩
  | true =>
    obtain ⟨d, hd⟩ := candidate_exists p.1.1 p.1.2 p.2 hi
    exact ⟨d, by simpa only [searchTest, hi, Bool.cond_true] using hd⟩

def search (p : Query) : Part Nat := Nat.rfind (fun d => Part.some (searchTest p d))

theorem search_partrec : Partrec search :=
  Partrec.rfind searchTest_primrec.to_comp.partrec.to₂

theorem search_total (p : Query) : (search p).Dom := by
  obtain ⟨d, hd⟩ := searchTest_exists p
  exact Nat.rfind_dom.mpr ⟨d, by simpa only [Part.mem_some_iff] using hd.symm,
    fun {_} _ => trivial⟩

def inverseCode (q root c : Nat) : Nat := (search ((q, root), c)).get
  (search_total ((q, root), c))

theorem inverseCode_computable : Computable
    (fun p : Query => inverseCode p.1.1 p.1.2 p.2) :=
  search_partrec.of_eq_tot (fun p => Part.get_mem (search_total p))

theorem inverseCode_test (q root c : Nat) :
    searchTest ((q, root), c) (inverseCode q root c) = true := by
  have h := Nat.rfind_spec (Part.get_mem (search_total ((q, root), c)))
  exact (Part.mem_some_iff.mp h).symm

/-- The ACTUAL computed finite inverse is an original accepted Normal
restricted source code and its literal iota output recovers raw target value. -/
theorem inverseCode_spec (q root c : Nat) (hi : inverseInput q root c = true) :
    Comparison.acceptedCode q (inverseCode q root c) = true ∧
      inputCheck q root (inverseCode q root c) = true ∧
      interpretation (betaCode q root) (literalCode q root (inverseCode q root c)) =
        interpretation (betaCode q root) c := by
  have ht : candidate q root c (inverseCode q root c) = true := by
    simpa only [searchTest, hi, Bool.cond_true] using inverseCode_test q root c
  have hs := (candidate_exact q root c _).mp ht
  have hn : Comparison.acceptedCode q (inverseCode q root c) = true := by
    exact (Bool.and_eq_true.mp (Bool.and_eq_true.mp hs.1).2).1
  exact ⟨hn, hs.1, hs.2.2⟩

theorem inverseCode_rejected (q root c : Nat) (hi : inverseInput q root c = false) :
    inverseCode q root c = 0 := by
  have ht := inverseCode_test q root c
  simpa only [searchTest, hi, Bool.cond_false, beq_iff_eq] using ht

/-- Genuine equality reflection gives the actual computed left inverse
on ORIGINAL admitted Normal restricted code inputs; spellings may differ. -/
theorem inverseCode_left_inverse (q root c : Nat) (hc : inputCheck q root c = true) :
    interpretation q (inverseCode q root (literalCode q root c)) = interpretation q c := by
  obtain ⟨ha, t, hcode, ht, hn, hstar⟩ := (inputCheck_exact q root c).mp hc
  have hi := (inverseInput_exact q root _).mpr ⟨ha, literalCode_checked q root c hc⟩
  have hs := inverseCode_spec q root _ hi
  exact (literalCode_eq_iff q root _ _ hs.2.1 hc).mp hs.2.2

theorem inverseCode_lt_iff (q root c d : Nat)
    (hc : inverseInput q root c = true) (hd : inverseInput q root d = true) :
    interpretation q (inverseCode q root c) < interpretation q (inverseCode q root d) ↔
      interpretation (betaCode q root) c < interpretation (betaCode q root) d := by
  have hs := inverseCode_spec q root c hc
  have hs' := inverseCode_spec q root d hd
  have he := literalCode_lt_iff q root _ _ hs.2.1 hs'.2.1
  rw [hs.2.2, hs'.2.2] at he
  exact he.symm

def execute (p : Query) : Part Nat := cond (inverseInput p.1.1 p.1.2 p.2)
  (Part.some (inverseCode p.1.1 p.1.2 p.2)) Part.none

theorem execute_partrec : Partrec execute := by
  have h := inverseInput_primrec.to_comp.cond
    (Computable.option_some.comp inverseCode_computable) (Computable.const Option.none)
  exact (Computable.ofOption h).of_eq (fun p => by
    cases hi : inverseInput p.1.1 p.1.2 p.2 <;>
      simp only [execute, hi, Bool.cond_true, Bool.cond_false] <;> rfl)

theorem execute_graph (q root c out : Nat) : out ∈ execute ((q, root), c) ↔
    inverseInput q root c = true ∧ out = inverseCode q root c := by
  cases hi : inverseInput q root c <;>
    simp only [execute, hi, Bool.cond_true, Bool.cond_false, Part.mem_some_iff,
      Part.notMem_none, Bool.false_eq_true, false_and, true_and, eq_comm]

theorem execute_domain (q root c : Nat) : (execute ((q, root), c)).Dom ↔
    rootCheck q root = true ∧ checkCode (betaCode q root) c = true := by
  constructor
  · intro h
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp h
    exact (inverseInput_exact q root c).mp ((execute_graph q root c out).mp ho).1
  · intro h
    exact Part.dom_iff_mem.mpr ⟨inverseCode q root c,
      (execute_graph q root c _).mpr ⟨(inverseInput_exact q root c).mpr h, rfl⟩⟩

theorem execute_spec (q root c out : Nat) (ho : out ∈ execute ((q, root), c)) :
    inverseInput q root c = true ∧ Comparison.acceptedCode q out = true ∧
      inputCheck q root out = true ∧
      interpretation (betaCode q root) (literalCode q root out) = interpretation (betaCode q root) c := by
  obtain ⟨hi, rfl⟩ := (execute_graph q root c out).mp ho
  exact ⟨hi, inverseCode_spec q root c hi⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Inverse
