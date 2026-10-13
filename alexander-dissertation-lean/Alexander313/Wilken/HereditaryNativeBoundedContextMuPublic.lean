import Alexander313.Wilken.HereditaryNativeBoundedContextMuTranslation
import Alexander313.Wilken.HereditaryNativeBoundedPublicReturnRaw

/-!
# Actual canonical public mu in the bounded intermediate context

The genuine translation theorem identifies the actual intermediate mu with
original-source mu at its constructed SAME-value returned beta root. The
original mu endpoint bound derives the real bounded public-return caller
there. This uses the returned beta root's own original endpoint, and does
not assume a bound at the original outer alpha-plus. The actual public
partial producer retains exactly the intermediate original guard and agrees
numerically with original-source canonical public mu. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.Mu.Public

open SourceReturn

def publicCode (s a root out : Nat) : Nat :=
  BoundedPublicReturn.publicCode s (returnedRoot s a root) out

theorem publicCode_primrec : Primrec₂
    (fun p : Context => publicCode p.1.1 p.1.2 p.2) :=
  (BoundedPublicReturn.publicCode_primrec.comp
    (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (returnedRoot_primrec.comp Primrec.fst)).pair Primrec.snd)).to₂

theorem execute_lt_returnedRoot_alphaPlus (s a root out : Nat)
    (ho : out ∈ Mu.execute s a root) :
    interpretation (betaCode s a root) out <
      Iota.AlphaPlus.sourceValue s (returnedRoot s a root) := by
  obtain ⟨ha, rfl⟩ := (Mu.execute_graph s a root out).mp ho
  have hb := NativeContext.Mu.Bounds.muCode_lt_source_alphaPlus s _
    (returnedRoot_iota_caller s a root ha)
  rw [returnedRoot_alphaCode s a root ha] at hb
  exact (Translation.muCode_value s a root ha).symm.trans_lt hb

theorem publicCode_caller (s a root out : Nat) (ho : out ∈ Mu.execute s a root) :
    BoundedPublicReturn.inputCheck s (returnedRoot s a root) out = true := by
  have hs := Mu.execute_spec s a root out ho
  apply (BoundedPublicReturn.inputCheck_exact s _ out).mpr
  refine ⟨returnedRoot_iota_caller s a root hs.1, ?_, ?_⟩
  · rw [returnedRoot_alphaCode s a root hs.1]
    exact hs.2.1
  · rw [returnedRoot_alphaCode s a root hs.1]
    exact execute_lt_returnedRoot_alphaPlus s a root out ho

theorem publicCode_spec (s a root out : Nat) (ho : out ∈ Mu.execute s a root) :
    Canonical.check (publicCode s a root out) = true ∧
      unionInterpretation (publicCode s a root out) = interpretation (betaCode s a root) out := by
  have hs := BoundedPublicReturn.publicCode_spec s _ out (publicCode_caller s a root out ho)
  rw [returnedRoot_alphaCode s a root (Mu.execute_spec s a root out ho).1] at hs
  exact hs

theorem sourceValue_translation (s a root : Nat) (ha : Mu.inputCheck s a root = true) :
    Mu.sourceValue s a root = NativeContext.Mu.sourceValue s (returnedRoot s a root) := by
  have hs := (NativeContext.Mu.muCode_spec s _ (returnedRoot_iota_caller s a root ha)).2.2
  rw [returnedRoot_alphaCode s a root ha] at hs
  exact (Mu.muCode_spec s a root ha).2.2.symm.trans
    ((Translation.muCode_value s a root ha).symm.trans hs)

/-- The actual finite code produced from intermediate mu is the SAME
canonical public number as original-source mu at the computed beta root. -/
theorem publicCode_agreement (s a root : Nat) (ha : Mu.inputCheck s a root = true) :
    publicCode s a root (Mu.muCode s a root) =
      BoundedPublicReturn.publicCode s (returnedRoot s a root)
        (NativeContext.Mu.muCode s (returnedRoot s a root)) := by
  have hn := (Mu.execute_graph s a root _).mpr ⟨ha, rfl⟩
  have ho := (NativeContext.Mu.execute_graph s _ _).mpr
    ⟨returnedRoot_iota_caller s a root ha, rfl⟩
  have hs := publicCode_spec s a root _ hn
  have ht := BoundedPublicReturn.mu_public_spec s _ _ ho
  rw [returnedRoot_alphaCode s a root ha] at ht
  exact Canonical.check_value_injective _ _ hs.1 ht.1
    (hs.2.trans ((Translation.muCode_value s a root ha).symm.trans ht.2.symm))

def execute (s a root : Nat) : Part Nat := (Mu.execute s a root).map (publicCode s a root)

theorem execute_partrec : Partrec (fun p : Context => execute p.1.1 p.1.2 p.2) :=
  Partrec.map Mu.execute_partrec publicCode_primrec.to_comp

theorem execute_domain (s a root : Nat) :
    (execute s a root).Dom ↔ Mu.inputCheck s a root = true := by
  simpa only [execute, Part.map] using Mu.execute_domain s a root

theorem execute_graph (s a root out : Nat) : out ∈ execute s a root ↔
    ∃ nativeOut ∈ Mu.execute s a root, publicCode s a root nativeOut = out :=
  Part.mem_map_iff (publicCode s a root)

theorem execute_spec (s a root out : Nat) (ho : out ∈ execute s a root) :
    Mu.inputCheck s a root = true ∧ Canonical.check out = true ∧
      unionInterpretation out = Mu.sourceValue s a root := by
  obtain ⟨nativeOut, hn, rfl⟩ := (execute_graph s a root out).mp ho
  have hs := Mu.execute_spec s a root nativeOut hn
  have hp := publicCode_spec s a root nativeOut hn
  exact ⟨hs.1, hp.1, hp.2.trans hs.2.2.2⟩

/-- On the original bounded intermediate root guard, both actual partial
executions have exactly the same canonical public numerical output. -/
theorem execute_eq_original_public (s a root : Nat) (ha : Mu.inputCheck s a root = true) :
    execute s a root = BoundedPublicReturn.muPublic s (returnedRoot s a root) := by
  have hroot : NativeContext.Mu.inputCheck s (returnedRoot s a root) = true :=
    returnedRoot_iota_caller s a root ha
  simp only [execute, Mu.execute, ha, Bool.cond_true, BoundedPublicReturn.muPublic,
    NativeContext.Mu.execute, hroot, Part.map_some, publicCode_agreement s a root ha]

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.BoundedContextIota.Mu.Public
