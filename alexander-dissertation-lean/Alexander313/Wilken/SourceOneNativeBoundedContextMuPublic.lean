import Alexander313.Wilken.SourceOneNativeBoundedContextMuTranslation
import Alexander313.Wilken.SourceOneNativeMuPublic

/-!
# Actual public mu over an original source-one outer root

The original source-zero outer root and genuine bounded intermediate root
derive the returned beta's OWN source alpha-plus caller. Actual source-one
mu translation proves the intermediate value lies below that endpoint; its
actual LOW output then executes the complete SAME-value public return.
The outer original endpoint is never substituted for the returned endpoint.
No return, bound or Program oracle. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextReturn.MuPublic

abbrev Context := Nat × Nat

def inputCheck (a b : Nat) : Bool := SourceOneIota.rootCheck a &&
  NativeContext.PublicEpsilonIota.Mu.inputCheck (alphaCode a) b

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp (rootCheck_primrec.comp Primrec.fst)
    (NativeContext.PublicEpsilonIota.rootCheck_primrec.comp
      (alphaCode_primrec.comp Primrec.fst) Primrec.snd)).to₂

theorem inputCheck_exact (a b : Nat) : inputCheck a b = true ↔
    SourceOneIota.rootCheck a = true ∧ NativeContext.PublicEpsilonIota.Mu.inputCheck (alphaCode a) b = true :=
  Bool.and_eq_true

def muCode (a b : Nat) : Nat := NativeContext.PublicEpsilonIota.Mu.muCode (alphaCode a) b

theorem muCode_primrec : Primrec₂ muCode :=
  (NativeContext.PublicEpsilonIota.Mu.muCode_primrec.comp
    ((alphaCode_primrec.comp Primrec.fst).pair Primrec.snd)).to₂

def nativeExecute (a b : Nat) : Part Nat := cond (inputCheck a b) (Part.some (muCode a b)) Part.none

theorem nativeExecute_partrec : Partrec₂ nativeExecute :=
  (Partrec.cond inputCheck_primrec.to_comp muCode_primrec.to_comp.partrec Partrec.none).to₂

theorem nativeExecute_domain (a b : Nat) : (nativeExecute a b).Dom ↔ inputCheck a b = true := by
  cases h : inputCheck a b <;> simp [nativeExecute, h]

theorem nativeExecute_graph (a b out : Nat) : out ∈ nativeExecute a b ↔
    inputCheck a b = true ∧ out = muCode a b := by
  cases h : inputCheck a b <;> simp [nativeExecute, h]

theorem nativeExecute_spec (a b out : Nat) (ho : out ∈ nativeExecute a b) :
    inputCheck a b = true ∧
      NativeContext.lowCheckCode (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b) out = true ∧
      NativeContext.Comparison.acceptedCode (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b) out = true ∧
      NativeContext.interpretation (NativeContext.PublicEpsilonIota.betaCode (alphaCode a) b) out =
        NativeContext.PublicEpsilonIota.Mu.sourceValue (alphaCode a) b := by
  obtain ⟨hi, rfl⟩ := (nativeExecute_graph a b out).mp ho
  exact ⟨hi, NativeContext.PublicEpsilonIota.Mu.muCode_spec _ _ ((inputCheck_exact a b).mp hi).2⟩

theorem returned_mu_caller (a b out : Nat) (ho : out ∈ nativeExecute a b) :
    BoundedPublicReturn.inputCheck (returnedRoot a b) out = true := by
  obtain ⟨hi, rfl⟩ := (nativeExecute_graph a b out).mp ho
  obtain ⟨ha, hb⟩ := (inputCheck_exact a b).mp hi
  have hr := returnedRoot_iota_caller a b ha hb
  have hs := NativeContext.PublicEpsilonIota.Mu.muCode_spec (alphaCode a) b hb
  have hl : NativeContext.lowCheckCode (SourceOneIota.alphaCode (returnedRoot a b)) (muCode a b) = true := by
    simpa only [returnedRoot_alphaCode a b ha hb, muCode] using hs.1
  have hbound : NativeContext.interpretation (SourceOneIota.alphaCode (returnedRoot a b)) (muCode a b) <
      Enclosure.sourceAlphaPlus (returnedRoot a b) := by
    rw [returnedRoot_alphaCode a b ha hb, muCode, ← MuTranslation.muCode_value a b ha hb]
    simpa only [returnedRoot_alphaCode a b ha hb] using
      SourceOneIota.Mu.Bounds.muCode_lt_source_alphaPlus (returnedRoot a b) hr
  exact (BoundedPublicReturn.inputCheck_exact _ _).mpr ⟨hr, hl, hbound⟩

def publicCode (a b out : Nat) : Nat := BoundedPublicReturn.publicCode (returnedRoot a b) out

theorem publicCode_primrec : Primrec₂ (fun p : Context => publicCode p.1 p.2) :=
  (BoundedPublicReturn.publicCode_primrec.comp (Primrec.comp returnedRoot_primrec Primrec.fst) Primrec.snd).to₂

theorem publicCode_spec (a b out : Nat) (ho : out ∈ nativeExecute a b) :
    Canonical.check (publicCode a b out) = true ∧
      unionInterpretation (publicCode a b out) = NativeContext.PublicEpsilonIota.Mu.sourceValue (alphaCode a) b := by
  have hi := (nativeExecute_spec a b out ho).1
  obtain ⟨ha, hb⟩ := (inputCheck_exact a b).mp hi
  have hp := BoundedPublicReturn.publicCode_spec _ out (returned_mu_caller a b out ho)
  rw [returnedRoot_alphaCode a b ha hb] at hp
  exact ⟨hp.1, hp.2.trans (nativeExecute_spec a b out ho).2.2.2⟩

def execute (a b : Nat) : Part Nat := (nativeExecute a b).map (publicCode a b)

theorem execute_partrec : Partrec₂ execute :=
  (Partrec.map nativeExecute_partrec publicCode_primrec.to_comp).to₂

theorem execute_domain (a b : Nat) : (execute a b).Dom ↔ inputCheck a b = true := by
  simpa only [execute, Part.map] using nativeExecute_domain a b

theorem execute_graph (a b out : Nat) : out ∈ execute a b ↔
    ∃ nativeOut ∈ nativeExecute a b, publicCode a b nativeOut = out := Part.mem_map_iff (publicCode a b)

theorem execute_spec (a b out : Nat) (ho : out ∈ execute a b) :
    inputCheck a b = true ∧ Canonical.check out = true ∧
      unionInterpretation out = NativeContext.PublicEpsilonIota.Mu.sourceValue (alphaCode a) b := by
  obtain ⟨nativeOut, hn, rfl⟩ := (execute_graph a b out).mp ho
  exact ⟨(nativeExecute_spec a b nativeOut hn).1, publicCode_spec a b nativeOut hn⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextReturn.MuPublic
