import Alexander313.Wilken.HereditaryGlobalMuDictionarySupport

/-!
# Executing the true extended canonical public mu

All canonical epsilons have an actual primitive recursive public result.
At a positive finite upsilon endpoint this is its real successor endpoint,
exactly Definition3.15. Outside the upsilon image it is literally the
independently executing proper public mu. The complete guarded partial
graph, positivity, principalness and genuine endpoint bounds are derived.
No global tracking or evaluation predicate defines this operation.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalMuDictionary

open Support

def publicCode (gamma : Nat) : Nat := cond (inputCheck gamma)
  (cond (PublicEpsilonSourceDictionary.basePoint gamma) (nextEndpointCode gamma)
    (MuPublicDictionary.publicCode gamma)) 0

theorem publicCode_primrec : Primrec publicCode := inputCheck_primrec.cond
  (PublicEpsilonSourceDictionary.basePoint_primrec.cond nextEndpointCode_primrec
    MuPublicDictionary.publicCode_primrec) (Primrec.const 0)

theorem publicCode_spec (gamma : Nat) (hi : inputCheck gamma = true) :
    Canonical.check (publicCode gamma) = true ∧ unionInterpretation (publicCode gamma) = sourceValue gamma := by
  cases hb : PublicEpsilonSourceDictionary.basePoint gamma with
  | true => simpa only [publicCode, sourceValue, hi, hb, Bool.cond_true] using nextEndpointCode_spec gamma
  | false => simpa only [publicCode, sourceValue, hi, hb, Bool.cond_true, Bool.cond_false] using
      MuPublicDictionary.publicCode_spec gamma (proper_caller gamma hi hb)

theorem publicCode_proper (gamma : Nat) (hi : MuPublicDictionary.Support.inputCheck gamma = true) :
    publicCode gamma = MuPublicDictionary.publicCode gamma := by
  have hs := (MuPublicDictionary.Support.inputCheck_exact gamma).mp hi
  simp only [publicCode, hs.1, hs.2, Bool.cond_true, Bool.cond_false]

/-- The actual successor endpoint spelling is determined by the real
least segment scan, without a caller-supplied endpoint index. -/
theorem publicCode_endpoint (n : Nat) :
    publicCode (PublicEpsilonSourceDictionary.endpointCode (n + 1)) =
      PublicEpsilonSourceDictionary.endpointCode ((n + 1) + 1) := by
  simp only [publicCode, endpoint_input, endpoint_basePoint, Bool.cond_true,
    nextEndpointCode, endpoint_level]

/-- This is the printed endpoint extension at every admitted basepoint:
mu(upsilon_k)=upsilon_(k+1), with the derived actual positive finite k. -/
theorem endpoint_extension (gamma : Nat) (hi : inputCheck gamma = true)
    (hb : PublicEpsilonSourceDictionary.basePoint gamma = true) :
    0 < PublicEpsilonSourceDictionary.level gamma ∧
      unionInterpretation gamma = sourceUpsilon ((PublicEpsilonSourceDictionary.level gamma : Nat) : Ordinal.{0}) ∧
        unionInterpretation (publicCode gamma) =
          sourceUpsilon ((PublicEpsilonSourceDictionary.level gamma + 1 : Nat) : Ordinal.{0}) := by
  have hs := base_point_spec gamma hi hb
  refine ⟨hs.1, hs.2.1, ?_⟩
  simpa only [sourceValue, hb, Bool.cond_true] using (publicCode_spec gamma hi).2

theorem publicCode_on_upsilon (gamma n : Nat) (hi : inputCheck gamma = true)
    (hv : unionInterpretation gamma = sourceUpsilon ((n + 1 : Nat) : Ordinal.{0})) :
    unionInterpretation (publicCode gamma) = sourceUpsilon (((n + 1) + 1 : Nat) : Ordinal.{0}) := by
  have hf : unionInterpretation gamma = finiteBase (n + 1) := hv.trans (PublicUpsilonSegment.successor_value n)
  have hl := SkPublicDictionary.FiniteDomain.level_eq_of_finiteBase gamma n hi hf
  have hb := (PublicEpsilonSourceDictionary.basePoint_exact gamma ((inputCheck_exact gamma).mp hi).1).mpr
    (by rw [hl]; exact hf)
  simpa only [hl] using (endpoint_extension gamma hi hb).2.2

/-- Actual membership in the semantic upsilon image derives the
basepoint branch and its positive finite successor index. -/
theorem image_extension (gamma : Nat) (hi : inputCheck gamma = true)
    (himage : SourceUpsilonImage (unionInterpretation gamma)) :
    0 < PublicEpsilonSourceDictionary.level gamma ∧
      unionInterpretation gamma = sourceUpsilon ((PublicEpsilonSourceDictionary.level gamma : Nat) : Ordinal.{0}) ∧
        unionInterpretation (publicCode gamma) =
          sourceUpsilon ((PublicEpsilonSourceDictionary.level gamma + 1 : Nat) : Ordinal.{0}) :=
  endpoint_extension gamma hi ((SkPublicDictionary.UpsilonDomain.basePoint_true_iff_image gamma hi).mpr himage)

theorem endpoint_increase (gamma : Nat) (hi : inputCheck gamma = true)
    (hb : PublicEpsilonSourceDictionary.basePoint gamma = true) :
    unionInterpretation gamma < unionInterpretation (publicCode gamma) := by
  have hs := endpoint_extension gamma hi hb
  rw [hs.2.1, hs.2.2, Nat.cast_succ]
  exact sourceUpsilon_step _

theorem publicCode_positive_principal (gamma : Nat) (hi : inputCheck gamma = true) :
    0 < unionInterpretation (publicCode gamma) ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation (publicCode gamma)) := by
  rw [(publicCode_spec gamma hi).2, sourceValue]
  cases hb : PublicEpsilonSourceDictionary.basePoint gamma with
  | true =>
    simp only [hb, Bool.cond_true, PublicUpsilonSegment.successor_value]
    have he := finiteBase_succ_omegaPower_eq_self (PublicEpsilonSourceDictionary.level gamma)
    refine ⟨finiteBase_pos _, ?_⟩
    rw [← he]
    exact Ordinal.isPrincipal_add_omega0_opow _
  | false => simpa only [hb, Bool.cond_false] using proper_value_positive_principal gamma (proper_caller gamma hi hb)

theorem publicCode_omega_le (gamma : Nat) (hi : inputCheck gamma = true) :
    Ordinal.omega0 ≤ unionInterpretation (publicCode gamma) := by
  rw [(publicCode_spec gamma hi).2, sourceValue]
  cases hb : PublicEpsilonSourceDictionary.basePoint gamma with
  | true =>
    simp only [hb, Bool.cond_true, PublicUpsilonSegment.successor_value]
    exact (epsilon_omega_lt (finiteBase_succ_omegaPower_eq_self _)).le
  | false => simpa only [hb, Bool.cond_false] using proper_value_omega_le gamma (proper_caller gamma hi hb)

/-- The extended result reaches the next endpoint exactly at a basepoint;
every proper result stays strictly inside that actual source grammar. -/
theorem publicCode_bound (gamma : Nat) (hi : inputCheck gamma = true) :
    unionInterpretation (publicCode gamma) ≤
      sourceUpsilon ((PublicEpsilonSourceDictionary.level gamma + 1 : Nat) : Ordinal.{0}) := by
  rw [(publicCode_spec gamma hi).2, sourceValue]
  cases hb : PublicEpsilonSourceDictionary.basePoint gamma with
  | true => simp only [hb, Bool.cond_true, le_refl]
  | false =>
    simpa only [hb, Bool.cond_false, PublicUpsilonSegment.successor_value] using
      (proper_value_bound gamma (proper_caller gamma hi hb)).le

theorem publicCode_proper_bound (gamma : Nat) (hi : MuPublicDictionary.Support.inputCheck gamma = true) :
    unionInterpretation (publicCode gamma) <
      sourceUpsilon ((PublicEpsilonSourceDictionary.level gamma + 1 : Nat) : Ordinal.{0}) := by
  rw [publicCode_proper gamma hi, (MuPublicDictionary.publicCode_spec gamma hi).2,
    PublicUpsilonSegment.successor_value]
  exact proper_value_bound gamma hi

def execute (gamma : Nat) : Part Nat := cond (inputCheck gamma) (Part.some (publicCode gamma)) Part.none

theorem execute_partrec : Partrec execute :=
  Partrec.cond inputCheck_primrec.to_comp publicCode_primrec.to_comp.partrec Partrec.none

theorem execute_domain (gamma : Nat) : (execute gamma).Dom ↔ inputCheck gamma = true := by
  cases hi : inputCheck gamma <;> simp [execute, hi]

theorem execute_domain_epsilon (gamma : Nat) : (execute gamma).Dom ↔
    Canonical.check gamma = true ∧ Ordinal.omega0 ^ unionInterpretation gamma = unionInterpretation gamma :=
  (execute_domain gamma).trans (inputCheck_exact gamma)

theorem execute_graph (gamma out : Nat) : out ∈ execute gamma ↔
    inputCheck gamma = true ∧ out = publicCode gamma := by
  cases hi : inputCheck gamma <;> simp [execute, hi]

theorem execute_returns (gamma : Nat) (hi : inputCheck gamma = true) : publicCode gamma ∈ execute gamma :=
  (execute_graph gamma _).mpr ⟨hi, rfl⟩

theorem execute_proper (gamma : Nat) (hi : MuPublicDictionary.Support.inputCheck gamma = true) :
    execute gamma = MuPublicDictionary.execute gamma := by
  have hg := (MuPublicDictionary.Support.inputCheck_exact gamma).mp hi
  simp only [execute, hg.1, MuPublicDictionary.execute, hi, Bool.cond_true, publicCode_proper gamma hi]

theorem execute_spec (gamma out : Nat) (ho : out ∈ execute gamma) :
    inputCheck gamma = true ∧ Canonical.check out = true ∧ unionInterpretation out = sourceValue gamma := by
  obtain ⟨hi, rfl⟩ := (execute_graph gamma out).mp ho
  exact ⟨hi, publicCode_spec gamma hi⟩

def graphBool (gamma out : Nat) : Bool := inputCheck gamma && (out == publicCode gamma)

theorem graphBool_primrec : Primrec₂ graphBool :=
  (Primrec.and.comp (inputCheck_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (publicCode_primrec.comp Primrec.fst))).to₂

theorem graphBool_exact (gamma out : Nat) : graphBool gamma out = true ↔ out ∈ execute gamma := by
  rw [execute_graph]
  simp only [graphBool, Bool.and_eq_true, beq_iff_eq]

theorem publicCode_equal_value (gamma other : Nat) (hi : inputCheck gamma = true)
    (hj : inputCheck other = true) (hv : unionInterpretation gamma = unionInterpretation other) :
    publicCode gamma = publicCode other :=
  congrArg publicCode (Canonical.check_value_injective gamma other ((inputCheck_exact gamma).mp hi).1
    ((inputCheck_exact other).mp hj).1 hv)

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalMuDictionary
