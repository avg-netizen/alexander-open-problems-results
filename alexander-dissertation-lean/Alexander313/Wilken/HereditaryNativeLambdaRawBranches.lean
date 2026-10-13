import Alexander313.Wilken.HereditaryNativeLambdaBranches

/-!
# Genuine normalize-first execution of both proper lambda branches

Every originally checked raw theta-zero tree is normalized by the existing
native algorithm before branch recognition. The exact domain is the original
raw proper root, not a supplied normalized-domain promise. Output admission
and context are derived from the actual normalized root. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.Branches.Raw

open NativePublicBridge (contextCode)

def normalizedRoot (s a : Nat) : Nat := Normalization.normalizeCode (contextCode s) a

theorem normalizedRoot_primrec : Primrec₂ normalizedRoot :=
  (Normalization.normalizeCode_primrec.comp
    (NativePublicBridge.contextCode_primrec.comp Primrec.fst) Primrec.snd).to₂

theorem normalizedRoot_theta (s : Nat) (t : RelativeTerm Nat)
    (ht : check (contextCode s) (.theta 0 t) = true) :
    normalizedRoot s (.theta 0 t : RelativeTerm Nat).code =
      (.theta 0 (Normalization.normalize (contextCode s) t) : RelativeTerm Nat).code := by
  simp only [normalizedRoot, Normalization.normalizeCode, checkCode_code, ht,
    Bool.cond_true, ThetaCourse.rawTree_code, Normalization.normalize]

def inputCheck (s a : Nat) : Bool := SourceZeta.rawInputCheck s a &&
  Branches.inputCheck s (normalizedRoot s a)

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp SourceZeta.rawInputCheck_primrec
    (Branches.inputCheck_primrec.comp Primrec.fst normalizedRoot_primrec)).to₂

theorem inputCheck_exact (s a : Nat) : inputCheck s a = true ↔
    ∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧
      check (contextCode s) (.theta 0 t) = true ∧
        base (contextCode s) < denote (contextCode s) (.theta 0 t) := by
  constructor
  · intro ha
    obtain ⟨hr, hn⟩ := Bool.and_eq_true.mp ha
    obtain ⟨t, he, ht⟩ := (SourceZeta.rawInputCheck_exact s a).mp hr
    obtain ⟨u, hu, huc, hun, hp⟩ := (Branches.inputCheck_exact s _).mp hn
    have hc : checkCode (contextCode s) a = true := (Bool.and_eq_true.mp hr).1
    have hv := (Normalization.normalizeCode_accepted (contextCode s) a hc).2
    have hnval : interpretation (contextCode s) (normalizedRoot s a) =
        interpretation (contextCode s) a := hv
    have hb : base (contextCode s) < interpretation (contextCode s) (normalizedRoot s a) := by
      simpa only [hu, interpretation_code] using hp
    exact ⟨t, he, ht, by simpa only [hnval, he, interpretation_code] using hb⟩
  · rintro ⟨t, rfl, ht, hp⟩
    have hs := Normalization.normalize_checked (contextCode s) (.theta 0 t) ht
    have he : Normalization.normalize (contextCode s) (.theta 0 t) =
        .theta 0 (Normalization.normalize (contextCode s) t) := rfl
    apply Bool.and_eq_true.mpr
    refine ⟨(SourceZeta.rawInputCheck_exact s _).mpr ⟨t, rfl, ht⟩, ?_⟩
    apply (Branches.inputCheck_exact s _).mpr
    refine ⟨Normalization.normalize (contextCode s) t, normalizedRoot_theta s t ht,
      ?_, ?_, ?_⟩
    · simpa only [he] using hs.1
    · simpa only [he, Comparison.Normal] using hs.2.1
    · have hv : denote (contextCode s) (.theta 0 (Normalization.normalize (contextCode s) t)) =
          denote (contextCode s) (.theta 0 t) := by
        simpa only [he] using hs.2.2
      rw [hv]
      exact hp

def execute (s a : Nat) : Part Nat := cond (inputCheck s a)
  (Branches.execute s (normalizedRoot s a)) Part.none

theorem execute_partrec : Partrec₂ execute := by
  have hp := Branches.execute_partrec.comp Primrec.fst.to_comp normalizedRoot_primrec.to_comp
  exact (Partrec.cond inputCheck_primrec.to_comp hp Partrec.none).to₂

theorem execute_domain (s a : Nat) : (execute s a).Dom ↔ inputCheck s a = true := by
  cases ha : inputCheck s a with
  | false => simp only [execute, ha, Bool.cond_false, Part.not_none_dom, Bool.false_eq_true]
  | true => simp only [execute, ha, Bool.cond_true, Branches.execute_domain,
      (Bool.and_eq_true.mp ha).2]

theorem execute_returns (s a : Nat) (ha : inputCheck s a = true) :
    ∃ out, out ∈ execute s a := Part.dom_iff_mem.mp ((execute_domain s a).mpr ha)

theorem execute_spec (s a out : Nat) (ho : out ∈ execute s a) :
    inputCheck s a = true ∧
      Comparison.acceptedCode (Branches.outputContext s (normalizedRoot s a)) out = true ∧
        interpretation (Branches.outputContext s (normalizedRoot s a)) out =
          Branches.sourceValue s (normalizedRoot s a) := by
  have ha := (execute_domain s a).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
  have hb : out ∈ Branches.execute s (normalizedRoot s a) := by
    simpa only [execute, ha, Bool.cond_true] using ho
  have hs := Branches.execute_spec s _ out hb
  exact ⟨ha, hs.2⟩

theorem branch_epsilon_iff_original (s a : Nat) (ha : inputCheck s a = true) :
    Iota.rootCheck s (normalizedRoot s a) = true ↔
      Ordinal.omega0 ^ interpretation (contextCode s) a = interpretation (contextCode s) a := by
  have hc := (Bool.and_eq_true.mp (Bool.and_eq_true.mp ha).1).1
  have hv := (Normalization.normalizeCode_accepted (contextCode s) a hc).2
  simpa only [normalizedRoot, hv] using
    Branches.high_iff_epsilon s _ (Bool.and_eq_true.mp ha).2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Lambda.Branches.Raw
