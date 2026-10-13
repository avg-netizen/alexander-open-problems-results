import Alexander313.Wilken.SourceOneNativeBoundedPublicReturnCodes

/-!
# Actual canonical public outputs of original source-one mu

Both normal and raw original mu executions are mapped through the genuine
bounded SAME-value finite return. Their complete original input domains
are retained. Raw conversion uses the actually computed normal root.
No native base-one parser or supplied return/value oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Mu.Public

/-- Execute normal mu and the actual bounded canonical SAME-value return. -/
def execute (a : Nat) : Part Nat := (Mu.execute a).map (BoundedPublicReturn.publicCode a)

theorem execute_partrec : Partrec execute :=
  Partrec.map Mu.execute_partrec BoundedPublicReturn.publicCode_primrec.to_comp

theorem execute_domain (a : Nat) : (execute a).Dom ↔ Mu.inputCheck a = true := by
  simpa only [execute, Part.map] using Mu.execute_domain a

theorem execute_graph (a out : Nat) : out ∈ execute a ↔
    ∃ nativeOut ∈ Mu.execute a, BoundedPublicReturn.publicCode a nativeOut = out :=
  Part.mem_map_iff (BoundedPublicReturn.publicCode a)

theorem execute_spec (a out : Nat) (ho : out ∈ execute a) :
    Mu.inputCheck a = true ∧ Canonical.check out = true ∧ unionInterpretation out = Mu.sourceValue a := by
  obtain ⟨nativeOut, hn, rfl⟩ := (execute_graph a out).mp ho
  have hs := Mu.execute_spec a nativeOut hn
  have hp := BoundedPublicReturn.mu_public_spec a nativeOut hn
  exact ⟨hs.1, hp.1, hp.2.trans hs.2.2.2⟩

def rawCode (a out : Nat) : Nat := BoundedPublicReturn.publicCode (Mu.Raw.normalizedRoot a) out

theorem rawCode_primrec : Primrec₂ rawCode :=
  BoundedPublicReturn.publicCode_primrec.comp (Mu.Raw.normalizedRoot_primrec.comp Primrec.fst) Primrec.snd

/-- Raw input executes the actual original normalizer before its computed
alpha-context mu output is returned at the SAME canonical public value. -/
def rawExecute (a : Nat) : Part Nat := (Mu.Raw.execute a).map (rawCode a)

theorem rawExecute_partrec : Partrec rawExecute := Partrec.map Mu.Raw.execute_partrec rawCode_primrec.to_comp

theorem rawExecute_domain (a : Nat) : (rawExecute a).Dom ↔ Mu.Raw.inputCheck a = true := by
  simpa only [rawExecute, Part.map] using Mu.Raw.execute_domain a

theorem rawExecute_domain_original (a : Nat) : (rawExecute a).Dom ↔
    (∃ t : RelativeTerm Nat, a = (.theta 0 t).code ∧ check 0 (.theta 0 t) = true) ∧
      Ordinal.omega0 ^ interpretation 0 a = interpretation 0 a := by
  rw [rawExecute_domain, Mu.Raw.inputCheck_exact]

theorem rawExecute_graph (a out : Nat) : out ∈ rawExecute a ↔
    ∃ nativeOut ∈ Mu.Raw.execute a, rawCode a nativeOut = out := Part.mem_map_iff (rawCode a)

theorem rawExecute_spec (a out : Nat) (ho : out ∈ rawExecute a) :
    Mu.Raw.inputCheck a = true ∧ Canonical.check out = true ∧
      unionInterpretation out = Mu.sourceValue (Mu.Raw.normalizedRoot a) := by
  obtain ⟨nativeOut, hn, rfl⟩ := (rawExecute_graph a out).mp ho
  have hs := Mu.Raw.execute_spec a nativeOut hn
  have hp := BoundedPublicReturn.raw_mu_public_spec a nativeOut hn
  exact ⟨hs.1, hp.1, hp.2.trans hs.2.2.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.Mu.Public
