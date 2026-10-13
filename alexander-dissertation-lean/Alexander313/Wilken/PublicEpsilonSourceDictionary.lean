import Alexander313.Wilken.PublicEpsilonSourceDictionarySupport
import Alexander313.Wilken.HereditaryNativePublicBridge

/-!
# Executing the original source dictionary of a canonical public epsilon

The finite endpoint scan separates an actual source base point from a proper
theta-zero root. Level zero uses the original source-one grammar. A positive
level uses the actual same-value native public bridge. Every root caller,
Normal proof and canonical alpha-code identity is derived. This does not
recode arbitrary native-q terms or prove invariance of mu across source bases.
Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.PublicEpsilonSourceDictionary

def basePoint (q : Nat) : Bool := Canonical.equal q (endpointCode (level q))

theorem basePoint_primrec : Primrec basePoint :=
  Canonical.Effective.equal_primrec.comp Primrec.id (endpointCode_primrec.comp level_primrec)

theorem basePoint_exact (q : Nat) (hq : Canonical.check q = true) :
    basePoint q = true ↔ unionInterpretation q = finiteBase (level q) := by
  simp only [basePoint, Canonical.equal_exact, hq, endpointCode_checked,
    endpointCode_value, true_and]

theorem proper_lower (q : Nat) (hq : inputCheck q = true) (hb : basePoint q = false) :
    finiteBase (level q) < unionInterpretation q := by
  apply lt_of_le_of_ne (level_lower q hq)
  intro he
  have ht := (basePoint_exact q ((inputCheck_exact q).mp hq).1).mpr he.symm
  rw [hb] at ht
  cases ht

def sourceRootCode (q : Nat) : Nat := (sourceTerm q).code

theorem sourceRootCode_primrec : Primrec sourceRootCode :=
  code_primrec.comp sourceTerm_primrec

theorem sourceRootCode_spec (q : Nat) (hq : inputCheck q = true) :
    ∃ b : RelativeTerm Nat, sourceRootCode q = (.theta 0 b).code ∧
      check (level q) (.theta 0 b) = true ∧ Theta.Normal (level q) (.theta 0 b) ∧
      interpretation (level q) (sourceRootCode q) = unionInterpretation q := by
  obtain ⟨b, hb, hc, hn, hv⟩ := sourceTerm_spec q hq
  refine ⟨b, by rw [sourceRootCode, hb], hc, hn, ?_⟩
  rw [sourceRootCode, interpretation_code, hb]
  exact hv

def sourceIndex (q : Nat) : Nat := level q - 1

theorem sourceIndex_primrec : Primrec sourceIndex :=
  Primrec.nat_sub.comp level_primrec (Primrec.const 1)

def positiveRootCode (q : Nat) : Nat :=
  NativePublicBridge.translateCode (sourceIndex q) (sourceRootCode q)

theorem positiveRootCode_primrec : Primrec positiveRootCode :=
  NativePublicBridge.translateCode_primrec.comp sourceIndex_primrec sourceRootCode_primrec

/-- A genuine base point has positive source level. Its native source base
is the original public epsilon itself, rather than a proper high root. -/
theorem base_point_spec (q : Nat) (hq : inputCheck q = true) (hb : basePoint q = true) :
    0 < level q ∧ NativeContext.baseCheck (NativePublicBridge.contextCode (sourceIndex q)) = true ∧
      NativeContext.base (NativePublicBridge.contextCode (sourceIndex q)) = unionInterpretation q := by
  have he := (inputCheck_exact q).mp hq
  have hv := (basePoint_exact q he.1).mp hb
  have hl : 0 < level q := by
    by_contra hn
    have hz : level q = 0 := by omega
    have h1 := EpsilonOffsets.epsilon_one_lt he.2
    rw [hv, hz, finiteBase_zero] at h1
    exact lt_irrefl _ h1
  refine ⟨hl, NativePublicBridge.contextCode_checked _, ?_⟩
  have hs : sourceIndex q + 1 = level q := by unfold sourceIndex; omega
  rw [NativePublicBridge.contextCode_value, hs]
  exact hv.symm

/-- Level zero is the actual original source-one dictionary. Epsilon is
strictly above its base one, so its returned root is genuinely high. -/
theorem source_one_spec (q : Nat) (hq : inputCheck q = true) (hl : level q = 0) :
    SourceOneIota.rootCheck (sourceRootCode q) = true ∧
      interpretation 0 (sourceRootCode q) = unionInterpretation q ∧
      q = SourceOneIota.alphaCode (sourceRootCode q) := by
  have hp : finiteBase (level q) < unionInterpretation q := by
    rw [hl, finiteBase_zero]
    exact EpsilonOffsets.epsilon_one_lt ((inputCheck_exact q).mp hq).2
  obtain ⟨b, hb, hc, hn, hs, hv⟩ := sourceTerm_high q hq hp
  have ha : sourceRootCode q = (.theta 0 b).code := by rw [sourceRootCode, hb]
  have hr : SourceOneIota.rootCheck (sourceRootCode q) = true :=
    (SourceOneIota.rootCheck_exact _).mpr
      ⟨b, ha, by simpa only [hl] using hc, by simpa only [hl] using hn, hs⟩
  have ht : interpretation 0 (sourceRootCode q) = unionInterpretation q := by
    rw [ha, interpretation_code]
    simpa only [hl] using hv
  have halpha := SourceOneIota.alphaCode_spec _ hr
  exact ⟨hr, ht, Canonical.check_value_injective _ _ ((inputCheck_exact q).mp hq).1
    halpha.1 (ht.symm.trans halpha.2.symm)⟩

/-- Positive proper roots are translated by the existing same-value source
bridge; the target alpha-code is literally the original canonical q. -/
theorem positive_spec (q s : Nat) (hq : inputCheck q = true)
    (hl : level q = s + 1) (hb : basePoint q = false) :
    sourceIndex q = s ∧ NativeContext.Iota.rootCheck s (positiveRootCode q) = true ∧
      NativeContext.interpretation (NativePublicBridge.contextCode s) (positiveRootCode q) =
        unionInterpretation q ∧ q = NativeContext.Iota.alphaCode s (positiveRootCode q) := by
  obtain ⟨b, hbterm, hc, hn, hs, hv⟩ := sourceTerm_high q hq (proper_lower q hq hb)
  have hindex : sourceIndex q = s := by unfold sourceIndex; omega
  have hsource : sourceRootCode q = (.theta 0 b).code := by rw [sourceRootCode, hbterm]
  have hroot : positiveRootCode q = (.theta 0 (NativePublicBridge.translate s b)).code := by
    rw [positiveRootCode, hindex, hsource, NativePublicBridge.translateCode_code,
      NativePublicBridge.translate_theta]
  have hcheck : NativeContext.check (NativePublicBridge.contextCode s)
      (.theta 0 (NativePublicBridge.translate s b)) = true := by
    rw [← NativePublicBridge.translate_theta, NativePublicBridge.translate_check]
    simpa only [hl] using hc
  have hnormal : NativeContext.Comparison.Normal (NativePublicBridge.contextCode s)
      (NativePublicBridge.translate s b) :=
    NativePublicBridge.translate_normal s b
      ((Theta.normal_theta (s + 1) 0 b).mp (by simpa only [hl] using hn))
  have hsort : 1 < (NativePublicBridge.translate s b).outerSort := by
    simpa only [NativePublicBridge.translate_outerSort] using hs
  have hr : NativeContext.Iota.rootCheck s (positiveRootCode q) = true :=
    (NativeContext.Iota.rootCheck_exact _ _).mpr ⟨_, hroot, hcheck, hnormal, hsort⟩
  have ht : NativeContext.interpretation (NativePublicBridge.contextCode s) (positiveRootCode q) =
      unionInterpretation q := by
    rw [positiveRootCode, hindex, NativePublicBridge.translateCode_value, hsource, interpretation_code]
    simpa only [hl] using hv
  have halpha := NativeContext.Iota.alphaCode_spec s _ hr
  exact ⟨hindex, hr, ht, Canonical.check_value_injective _ _ ((inputCheck_exact q).mp hq).1
    halpha.1 (ht.symm.trans halpha.2.symm)⟩

/-- Tag zero is a base point, one is an original source-one root, two is a
proper positive-context root, and three is an invalid public input. -/
def tag (q : Nat) : Nat := cond (inputCheck q)
  (cond (basePoint q) 0 (cond (level q == 0) 1 2)) 3

theorem tag_primrec : Primrec tag :=
  inputCheck_primrec.cond
    (basePoint_primrec.cond (Primrec.const 0)
      ((Primrec.beq.comp level_primrec (Primrec.const 0)).cond (Primrec.const 1) (Primrec.const 2)))
    (Primrec.const 3)

theorem tag_invalid (q : Nat) (hq : inputCheck q = false) : tag q = 3 := by
  simp only [tag, hq, Bool.cond_false]

/-- The original public epsilon guard alone supplies one of the three real
source dictionaries, including exact public alpha identity in each root case. -/
theorem dictionary_spec (q : Nat) (hq : inputCheck q = true) :
    (tag q = 0 ∧ 0 < level q ∧
      NativeContext.baseCheck (NativePublicBridge.contextCode (sourceIndex q)) = true ∧
      NativeContext.base (NativePublicBridge.contextCode (sourceIndex q)) = unionInterpretation q) ∨
    (tag q = 1 ∧ SourceOneIota.rootCheck (sourceRootCode q) = true ∧
      interpretation 0 (sourceRootCode q) = unionInterpretation q ∧
      q = SourceOneIota.alphaCode (sourceRootCode q)) ∨
    (tag q = 2 ∧ NativeContext.Iota.rootCheck (sourceIndex q) (positiveRootCode q) = true ∧
      NativeContext.interpretation (NativePublicBridge.contextCode (sourceIndex q)) (positiveRootCode q) =
        unionInterpretation q ∧ q = NativeContext.Iota.alphaCode (sourceIndex q) (positiveRootCode q)) := by
  cases hb : basePoint q with
  | true =>
    exact Or.inl ⟨by simp only [tag, hq, hb, Bool.cond_true], base_point_spec q hq hb⟩
  | false =>
    cases hl : level q with
    | zero =>
      exact Or.inr (Or.inl ⟨by simp only [tag, hq, hb, hl, beq_self_eq_true,
        Bool.cond_true, Bool.cond_false], source_one_spec q hq hl⟩)
    | succ s =>
      have hp := positive_spec q s hq hl hb
      have hz : (s + 1 == 0) = false := by simp
      have ht : tag q = 2 := by
        simp only [tag, hq, hb, hl, hz, Bool.cond_true,
          Bool.cond_false]
      exact Or.inr (Or.inr ⟨ht, by simpa only [hp.1] using hp.2⟩)

end Alexander313.Wilken.RelativeTerm.Hereditary.PublicEpsilonSourceDictionary
