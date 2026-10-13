import Alexander313.Wilken.SourceOneNativeLambdaPublicBranches

/-!
# BOTH original raw source-one lambda branches

The actual ORIGINAL source-zero normalizer runs before branch recognition.
The complete domain is ORIGINAL raw admitted theta-zero roots strictly
above one. The selected high branch is exactly ORIGINAL epsilon status.
Both branches execute canonical SAME-value public output without a Normal,
selected-base, epsilon-only or supplied-return guard. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Lambda.PublicBranches.Raw

abbrev normalizedRoot := Mu.Raw.normalizedRoot

theorem normalizedRoot_primrec : Primrec normalizedRoot := Mu.Raw.normalizedRoot_primrec

def inputCheck (a : Nat) : Bool := SourceZeta.rawInputCheck 0 a &&
  PublicBranches.inputCheck (normalizedRoot a)

theorem inputCheck_primrec : Primrec inputCheck :=
  Primrec.and.comp (SourceZeta.rawInputCheck_primrec.comp (Primrec.const 0) Primrec.id)
    (PublicBranches.inputCheck_primrec.comp normalizedRoot_primrec)

theorem inputCheck_exact (a : Nat) : inputCheck a = true ↔
    ∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧ check 0 (.theta 0 t) = true ∧
      1 < denote 0 (.theta 0 t) := by
  constructor
  · intro ha
    obtain ⟨hr, hn⟩ := Bool.and_eq_true.mp ha
    obtain ⟨t, he, ht⟩ := (SourceZeta.rawInputCheck_exact 0 a).mp hr
    obtain ⟨u, hu, huc, hun, hp⟩ := (PublicBranches.inputCheck_exact _).mp hn
    have hc : checkCode 0 a = true := (Bool.and_eq_true.mp hr).1
    have hv := (Theta.Normalization.normalizeCode_checked 0 a hc).2.2
    have hnv : interpretation 0 (normalizedRoot a) = interpretation 0 a := hv
    have hb : 1 < interpretation 0 (normalizedRoot a) := by
      simpa only [hu, interpretation_code] using hp
    exact ⟨t, he, ht, by simpa only [hnv, he, interpretation_code] using hb⟩
  · rintro ⟨t, rfl, ht, hp⟩
    have hr := (SourceZeta.rawInputCheck_exact 0 _).mpr ⟨t, rfl, ht⟩
    have hi := SourceZeta.raw_normalized_input 0 _ hr
    obtain ⟨u, hu, hc, hn⟩ := (SourceZeta.inputCheck_exact 0 (normalizedRoot (.theta 0 t : RelativeTerm Nat).code)).mp hi
    have hv := (Theta.Normalization.normalizeCode_checked 0 _ (Bool.and_eq_true.mp hr).1).2.2
    refine Bool.and_eq_true.mpr ⟨hr, (PublicBranches.inputCheck_exact _).mpr ⟨u, hu, hc, hn, ?_⟩⟩
    have hproper : 1 < interpretation 0 (.theta 0 t : RelativeTerm Nat).code := by
      simpa only [interpretation_code] using hp
    have he : denote 0 (.theta 0 u) = interpretation 0 (.theta 0 t : RelativeTerm Nat).code := by
      rw [← interpretation_code, ← hu]
      exact hv
    rw [he]
    exact hproper

theorem high_iff_epsilon (a : Nat) (ha : inputCheck a = true) :
    rootCheck (normalizedRoot a) = true ↔
      Ordinal.omega0 ^ interpretation 0 a = interpretation 0 a := by
  have hc := (Bool.and_eq_true.mp (Bool.and_eq_true.mp ha).1).1
  have hv := (Theta.Normalization.normalizeCode_checked 0 a hc).2.2
  simpa only [normalizedRoot, Mu.Raw.normalizedRoot, hv] using
    PublicBranches.high_iff_epsilon _ (Bool.and_eq_true.mp ha).2

noncomputable def sourceValue (a : Nat) : Ordinal.{0} := PublicBranches.sourceValue (normalizedRoot a)

theorem zeta_sourceValue_normalized (a : Nat) (ha : inputCheck a = true) :
    SourceZeta.sourceValue 0 (normalizedRoot a) = SourceZeta.sourceValue 0 a := by
  apply SourceZeta.sourceValue_argument_congr 0
  exact SourceZeta.raw_argument_value 0 a (Bool.and_eq_true.mp ha).1

theorem source_definition_2_45 (a : Nat) (ha : inputCheck a = true) : sourceValue a =
    if Ordinal.omega0 ^ interpretation 0 a = interpretation 0 a then
      NativeContext.interpretation (alphaCode (normalizedRoot a))
        (literalCode (normalizedRoot a) (Lambda.deltaCode (normalizedRoot a))) +
          SourceZeta.sourceValue 0 a
    else SourceZeta.sourceValue 0 a := by
  rw [← high_iff_epsilon a ha]
  simp only [sourceValue, PublicBranches.sourceValue, zeta_sourceValue_normalized a ha]

def execute (a : Nat) : Part Nat := cond (inputCheck a)
  (PublicBranches.execute (normalizedRoot a)) Part.none

theorem execute_partrec : Partrec execute :=
  Partrec.cond inputCheck_primrec.to_comp
    (PublicBranches.execute_partrec.comp normalizedRoot_primrec.to_comp) Partrec.none

theorem execute_domain (a : Nat) : (execute a).Dom ↔ inputCheck a = true := by
  cases ha : inputCheck a with
  | false => simp only [execute, ha, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true => simp only [execute, ha, Bool.cond_true, PublicBranches.execute_domain,
      (Bool.and_eq_true.mp ha).2]

theorem execute_domain_original (a : Nat) : (execute a).Dom ↔
    ∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧ check 0 (.theta 0 t) = true ∧
      1 < denote 0 (.theta 0 t) := by
  rw [execute_domain, inputCheck_exact]

theorem execute_returns (a : Nat) (ha : inputCheck a = true) : ∃ out, out ∈ execute a :=
  Part.dom_iff_mem.mp ((execute_domain a).mpr ha)

theorem execute_graph (a out : Nat) : out ∈ execute a ↔
    inputCheck a = true ∧ out ∈ PublicBranches.execute (normalizedRoot a) := by
  cases h : inputCheck a <;> simp [execute, h]

theorem execute_spec (a out : Nat) (ho : out ∈ execute a) :
    inputCheck a = true ∧ Canonical.check out = true ∧ unionInterpretation out = sourceValue a := by
  obtain ⟨ha, hn⟩ := (execute_graph a out).mp ho
  exact ⟨ha, (PublicBranches.execute_spec _ out hn).2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Lambda.PublicBranches.Raw
