import Alexander313.Wilken.SourceOneNativeBoundedPublicReturnCodes

/-!
# Actual public execution of BOTH original source-one lambda branches

The original admitted Normal theta-zero root must have value strictly
above one. Its genuine high-root test is exactly its epsilon status.
The epsilon branch executes the real iota-plus-zeta lambda and its full
bounded SAME-value public return. The non-epsilon branch executes actual
source-zero zeta, whose output is already canonical public. Source base
one is never passed to the native epsilon parser. No branch, return,
Normality or selected-context oracle. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Lambda.PublicBranches

def inputCheck (a : Nat) : Bool := SourceZeta.inputCheck 0 a &&
  Theta.Normalization.lessRawCode 0 OmegaQuotient.unitTerm.code a

theorem inputCheck_primrec : Primrec inputCheck :=
  Primrec.and.comp (SourceZeta.inputCheck_primrec.comp (Primrec.const 0) Primrec.id)
    (Theta.Normalization.Effective.lessRawCode_primrec.comp
      ((Primrec.const 0).pair ((Primrec.const OmegaQuotient.unitTerm.code).pair Primrec.id)))

theorem inputCheck_exact (a : Nat) : inputCheck a = true ↔
    ∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧ check 0 (.theta 0 t) = true ∧
      Theta.Normal 0 (.theta 0 t) ∧ 1 < denote 0 (.theta 0 t) := by
  have hu : checkCode 0 OmegaQuotient.unitTerm.code = true := by
    simpa only [checkCode_code] using OmegaQuotient.unitTerm_spec.1
  constructor
  · intro ha
    have hs := Bool.and_eq_true.mp ha
    obtain ⟨t, he, ht, hn⟩ := (SourceZeta.inputCheck_exact 0 a).mp hs.1
    have hc : checkCode 0 a = true := by simpa only [he, checkCode_code] using ht
    have hv := (Theta.Normalization.lessRawCode_correct 0 _ a hu hc).mp hs.2
    exact ⟨t, he, ht, hn, by simpa only [interpretation_code, OmegaQuotient.unitTerm_spec.2.2, he] using hv⟩
  · rintro ⟨t, rfl, ht, hn, hp⟩
    have hc : checkCode 0 (.theta 0 t : RelativeTerm Nat).code = true := by
      simpa only [checkCode_code] using ht
    refine Bool.and_eq_true.mpr ⟨(SourceZeta.inputCheck_exact 0 _).mpr ⟨t, rfl, ht, hn⟩, ?_⟩
    apply (Theta.Normalization.lessRawCode_correct 0 _ _ hu hc).mpr
    simpa only [interpretation_code, OmegaQuotient.unitTerm_spec.2.2] using hp

theorem original_input (a : Nat) (ha : inputCheck a = true) : SourceZeta.inputCheck 0 a = true :=
  (Bool.and_eq_true.mp ha).1

theorem high_iff_epsilon (a : Nat) (ha : inputCheck a = true) :
    rootCheck a = true ↔ Ordinal.omega0 ^ interpretation 0 a = interpretation 0 a := by
  constructor
  · exact root_epsilon a
  · intro he
    obtain ⟨t, ht, hc, hn, hp⟩ := (inputCheck_exact a).mp ha
    have he' : Ordinal.omega0 ^ denote 0 (.theta 0 t) = denote 0 (.theta 0 t) := by
      simpa only [ht, interpretation_code] using he
    have hh : 1 < t.outerSort := by
      simpa only [Nat.zero_add, lt_self_iff_false, or_self, and_false, or_false] using
        (Epsilon.theta_epsilon_iff 0 0 t hc).mp he'
    exact (rootCheck_exact a).mpr ⟨t, ht, hc, hn, hh⟩

theorem high_input (a : Nat) (ha : rootCheck a = true) : inputCheck a = true := by
  obtain ⟨t, he, ht, hn, hh⟩ := (rootCheck_exact a).mp ha
  apply (inputCheck_exact a).mpr
  refine ⟨t, he, ht, hn, ?_⟩
  simpa only [← he, ← interpretation_code] using EpsilonOffsets.epsilon_one_lt (root_epsilon a ha)

noncomputable def sourceValue (a : Nat) : Ordinal.{0} :=
  if rootCheck a = true then
    NativeContext.interpretation (alphaCode a) (literalCode a (Lambda.deltaCode a)) +
      SourceZeta.sourceValue 0 a
  else SourceZeta.sourceValue 0 a

theorem source_definition_2_45 (a : Nat) (ha : inputCheck a = true) : sourceValue a =
    if Ordinal.omega0 ^ interpretation 0 a = interpretation 0 a then
      NativeContext.interpretation (alphaCode a) (literalCode a (Lambda.deltaCode a)) +
        SourceZeta.sourceValue 0 a
    else SourceZeta.sourceValue 0 a := by
  rw [← high_iff_epsilon a ha]
  rfl

def execute (a : Nat) : Part Nat := cond (inputCheck a)
  (cond (rootCheck a) ((Lambda.execute a).map (BoundedPublicReturn.publicCode a))
    (SourceZeta.zeta 0 a)) Part.none

theorem execute_partrec : Partrec execute :=
  Partrec.cond inputCheck_primrec.to_comp
    (Partrec.cond rootCheck_primrec.to_comp
      (Partrec.map Lambda.execute_partrec BoundedPublicReturn.publicCode_primrec.to_comp)
      (SourceZeta.zeta_partrec.comp (Computable.const 0) Computable.id)) Partrec.none

theorem execute_domain (a : Nat) : (execute a).Dom ↔ inputCheck a = true := by
  cases ha : inputCheck a with
  | false => simp only [execute, ha, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true =>
    cases hh : rootCheck a with
    | false => simp only [execute, ha, hh, Bool.cond_true, Bool.cond_false,
        SourceZeta.zeta_domain, original_input a ha]
    | true => simp only [execute, ha, hh, Bool.cond_true, Part.map, Lambda.execute_domain, hh]

theorem execute_returns (a : Nat) (ha : inputCheck a = true) : ∃ out, out ∈ execute a :=
  Part.dom_iff_mem.mp ((execute_domain a).mpr ha)

theorem execute_spec (a out : Nat) (ho : out ∈ execute a) :
    inputCheck a = true ∧ Canonical.check out = true ∧ unionInterpretation out = sourceValue a := by
  have ha := (execute_domain a).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  cases hh : rootCheck a with
  | false =>
    have hz : out ∈ SourceZeta.zeta 0 a := by
      simpa only [execute, ha, hh, Bool.cond_true, Bool.cond_false] using ho
    have hs := SourceZeta.zeta_value 0 a out hz
    exact ⟨ha, hs.2.1, by simpa only [sourceValue, hh, Bool.false_eq_true, if_false] using hs.2.2⟩
  | true =>
    have hm : out ∈ (Lambda.execute a).map (BoundedPublicReturn.publicCode a) := by
      simpa only [execute, ha, hh, Bool.cond_true] using ho
    obtain ⟨nativeOut, hn, rfl⟩ := (Part.mem_map_iff (BoundedPublicReturn.publicCode a)).mp hm
    have hn' := Lambda.execute_spec a nativeOut hn
    have hp := BoundedPublicReturn.lambda_public_spec a nativeOut hn
    exact ⟨ha, hp.1, by simpa only [sourceValue, hh, if_pos rfl] using hp.2.trans hn'.2.2⟩

theorem execute_high (a : Nat) (ha : rootCheck a = true) : execute a =
    (Lambda.execute a).map (BoundedPublicReturn.publicCode a) := by
  simp only [execute, high_input a ha, ha, Bool.cond_true]

theorem execute_low (a : Nat) (ha : inputCheck a = true) (hh : rootCheck a = false) :
    execute a = SourceZeta.zeta 0 a := by
  simp only [execute, ha, hh, Bool.cond_true, Bool.cond_false]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Lambda.PublicBranches
