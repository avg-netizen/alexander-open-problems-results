import Alexander313.Wilken.HereditarySkPublicDictionarySupport

/-!
# Executing canonical public sk at its selected original source

The actual finite proper-epsilon dictionary selects its original source-one
or positive-source root and invokes the genuine terminating sk procedure.
Every output is canonical public syntax and has an entire original-source
maximal recurrence certificate with the original initial ordinal value.
Equal admitted canonical root and cutoff values identify the complete
numeric output. Finite-base endpoints remain explicitly excluded by the
real guard; no equivalence with global Im(upsilon), arbitrary cross-source
mu identity, assigned global tracking word, Par or evaluation is claimed.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicDictionary

open Support

def execute (p : Query) : Part (List Nat) := cond (inputCheck p.1 p.2)
  (cond (PublicEpsilonSourceDictionary.level p.1 == 0)
    (sourceOneExecute (PublicEpsilonSourceDictionary.sourceRootCode p.1, p.2))
    (NativeContext.PublicEpsilonUnboundedIota.SkSourceWord.executePublic (nativeQuery p.1 p.2))) Part.none

theorem execute_partrec : Partrec execute := by
  have hs := sourceOneExecute_partrec.comp
    ((PublicEpsilonSourceDictionary.sourceRootCode_primrec.comp Primrec.fst).pair Primrec.snd).to_comp
  have hn := NativeContext.PublicEpsilonUnboundedIota.SkSourceWord.executePublic_partrec.comp
    nativeQuery_primrec.to_comp
  have hb := Primrec.beq.comp (PublicEpsilonSourceDictionary.level_primrec.comp Primrec.fst)
    (Primrec.const 0)
  exact Partrec.cond inputCheck_primrec.to_comp (Partrec.cond hb.to_comp hs hn) Partrec.none

theorem execute_domain (gamma cutoff : Nat) : (execute (gamma, cutoff)).Dom ↔
    inputCheck gamma cutoff = true := by
  constructor
  · intro hd
    cases hi : inputCheck gamma cutoff with
    | true => rfl
    | false =>
      have hn : (Part.none : Part (List Nat)).Dom := by
        simpa only [execute, hi, Bool.cond_false] using hd
      exact False.elim (Part.not_none_dom hn)
  · intro hi
    cases hb : PublicEpsilonSourceDictionary.level gamma == 0 with
    | true =>
      have hl := beq_iff_eq.mp hb
      have hd := (sourceOneExecute_domain _ cutoff).mpr (sourceOne_caller gamma cutoff hi hl)
      simpa only [execute, hi, hb, Bool.cond_true] using hd
    | false =>
      have hl : PublicEpsilonSourceDictionary.level gamma ≠ 0 := by
        intro he
        have ht : (PublicEpsilonSourceDictionary.level gamma == 0) = true := beq_iff_eq.mpr he
        rw [hb] at ht
        cases ht
      have hd := (NativeContext.PublicEpsilonUnboundedIota.SkSourceWord.executePublic_domain _ _ cutoff).mpr
        (native_caller gamma cutoff hi hl)
      simpa only [execute, hi, hb, Bool.cond_true, Bool.cond_false] using hd

theorem execute_returns (gamma cutoff : Nat) (hi : inputCheck gamma cutoff = true) :
    ∃ codes, codes ∈ execute (gamma, cutoff) :=
  Part.dom_iff_mem.mp ((execute_domain gamma cutoff).mpr hi)

theorem execute_cases (gamma cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ execute (gamma, cutoff)) : inputCheck gamma cutoff = true ∧
    ((PublicEpsilonSourceDictionary.level gamma = 0 ∧
        codes ∈ sourceOneExecute (PublicEpsilonSourceDictionary.sourceRootCode gamma, cutoff)) ∨
      (PublicEpsilonSourceDictionary.level gamma ≠ 0 ∧
        codes ∈ NativeContext.PublicEpsilonUnboundedIota.SkSourceWord.executePublic (nativeQuery gamma cutoff))) := by
  have hi := (execute_domain gamma cutoff).mp (Part.dom_iff_mem.mpr ⟨codes, ho⟩)
  refine ⟨hi, ?_⟩
  cases hb : PublicEpsilonSourceDictionary.level gamma == 0 with
  | true =>
    exact Or.inl ⟨beq_iff_eq.mp hb,
      by simpa only [execute, hi, hb, Bool.cond_true] using ho⟩
  | false =>
    have hl : PublicEpsilonSourceDictionary.level gamma ≠ 0 := by
      intro he
      have ht : (PublicEpsilonSourceDictionary.level gamma == 0) = true := beq_iff_eq.mpr he
      rw [hb] at ht
      cases ht
    exact Or.inr ⟨hl, by simpa only [execute, hi, hb, Bool.cond_true, Bool.cond_false] using ho⟩

/-- The selected-source certificate includes the actual original-source
execution, complete maximal recurrence and unchanged original initial value. -/
def SelectedSource (gamma cutoff : Nat) (codes : List Nat) : Prop :=
  (PublicEpsilonSourceDictionary.level gamma = 0 ∧ ∃ source,
    source ∈ SourceOneIota.SkSourceWord.execute (PublicEpsilonSourceDictionary.sourceRootCode gamma, cutoff) ∧
    SourceOneIota.SkSourceRecurrence.SourcePath cutoff source ∧
    codes.map unionInterpretation = source.map (interpretation 0) ∧
    ∃ a xs, source = a :: xs ∧ interpretation 0 a = unionInterpretation gamma) ∨
  (PublicEpsilonSourceDictionary.level gamma ≠ 0 ∧ ∃ source,
    source ∈ NativeContext.PublicEpsilonUnboundedIota.SkSourceWord.execute (nativeQuery gamma cutoff) ∧
    NativeContext.PublicEpsilonUnboundedIota.SkSourceRecurrence.SourcePath
      (nativeQuery gamma cutoff).1.1 cutoff source ∧
    codes.map unionInterpretation = source.map (NativeContext.interpretation (nativeQuery gamma cutoff).1.1) ∧
    ∃ a xs, source = a :: xs ∧
      NativeContext.interpretation (nativeQuery gamma cutoff).1.1 a = unionInterpretation gamma)

/-- Actual execution alone derives canonical syntax and a complete genuine
selected-original-source maximal recurrence, with all source callers internal. -/
theorem execute_spec (gamma cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ execute (gamma, cutoff)) : inputCheck gamma cutoff = true ∧
      (∀ c ∈ codes, Canonical.check c = true) ∧ SelectedSource gamma cutoff codes := by
  obtain ⟨hi, hcases⟩ := execute_cases gamma cutoff codes ho
  rcases hcases with ⟨hl, hs⟩ | ⟨hl, hn⟩
  · obtain ⟨hinput, hc, source, hsource, he, hv⟩ := sourceOneExecute_spec _ cutoff codes hs
    have hp := SourceOneIota.SkSourceRecurrence.execute_source _ cutoff source hsource
    obtain ⟨xs, hhead⟩ := (SourceOneIota.SkSourceWord.execute_spec _ cutoff source hsource).2.2.1
    have hvalue := (PublicEpsilonSourceDictionary.source_one_spec gamma
      ((inputCheck_exact gamma cutoff).mp hi).1 hl).2.1
    exact ⟨hi, hc, Or.inl ⟨hl, source, hsource, hp, hv, _, xs, hhead, hvalue⟩⟩
  · have hinput := native_caller gamma cutoff hi hl
    obtain ⟨source, hs⟩ := NativeContext.PublicEpsilonUnboundedIota.SkSourceWord.execute_returns _ _ cutoff hinput
    have hp := NativeContext.PublicEpsilonUnboundedIota.SkSourceRecurrence.execute_spec _ _ cutoff source hs
    have hv := NativeContext.PublicEpsilonUnboundedIota.SkPublicValueInvariance.public_source_values
      _ _ cutoff codes source hn hs
    obtain ⟨a, xs, hsource, hvalue, hpos, hterminal⟩ := hp.2
    have hg := (native_root gamma cutoff hi hl).2
    exact ⟨hi, (NativeContext.PublicEpsilonUnboundedIota.SkSourceWord.executePublic_spec _ _ cutoff codes hn).2.1,
      Or.inr ⟨hl, source, hs, hp.1, hv, a, xs, hsource, hvalue.trans hg⟩⟩

theorem execute_nonempty (gamma cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ execute (gamma, cutoff)) : codes ≠ [] := by
  have hs := (execute_spec gamma cutoff codes ho).2.2
  rcases hs with ⟨hl, source, hsource, hp, hv, a, xs, hhead, hvalue⟩ |
    ⟨hl, source, hsource, hp, hv, a, xs, hhead, hvalue⟩ <;>
    intro hn <;> rw [hn, hhead, List.map_nil, List.map_cons] at hv <;>
    exact List.cons_ne_nil _ _ hv.symm

/-- Equal canonical initial and public cutoff values give literally the
same entire selected-source canonical public word. -/
theorem execute_eq (gamma other cutoff otherCutoff : Nat) (codes otherCodes : List Nat)
    (ho : codes ∈ execute (gamma, cutoff)) (ht : otherCodes ∈ execute (other, otherCutoff))
    (hgamma : unionInterpretation gamma = unionInterpretation other)
    (hcut : unionInterpretation cutoff = unionInterpretation otherCutoff) : codes = otherCodes := by
  have hi := (execute_cases gamma cutoff codes ho).1
  have hj := (execute_cases other otherCutoff otherCodes ht).1
  have he := Canonical.check_value_injective gamma other
    ((PublicEpsilonSourceDictionary.inputCheck_exact gamma).mp ((inputCheck_exact gamma cutoff).mp hi).1).1
    ((PublicEpsilonSourceDictionary.inputCheck_exact other).mp ((inputCheck_exact other otherCutoff).mp hj).1).1 hgamma
  subst other
  cases hb : PublicEpsilonSourceDictionary.level gamma == 0 with
  | true =>
    have hs : codes ∈ sourceOneExecute (PublicEpsilonSourceDictionary.sourceRootCode gamma, cutoff) := by
      simpa only [execute, hi, hb, Bool.cond_true] using ho
    have hother : otherCodes ∈ sourceOneExecute (PublicEpsilonSourceDictionary.sourceRootCode gamma, otherCutoff) := by
      simpa only [execute, hj, hb, Bool.cond_true] using ht
    exact sourceOneExecute_eq _ _ cutoff otherCutoff codes otherCodes hs hother rfl hcut
  | false =>
    have hs : codes ∈ NativeContext.PublicEpsilonUnboundedIota.SkSourceWord.executePublic (nativeQuery gamma cutoff) := by
      simpa only [execute, hi, hb, Bool.cond_true, Bool.cond_false] using ho
    have hother : otherCodes ∈ NativeContext.PublicEpsilonUnboundedIota.SkSourceWord.executePublic (nativeQuery gamma otherCutoff) := by
      simpa only [execute, hj, hb, Bool.cond_true, Bool.cond_false] using ht
    exact NativeContext.PublicEpsilonUnboundedIota.SkPublicValueInvariance.executePublic_eq
      _ _ _ cutoff otherCutoff codes otherCodes hs hother rfl hcut

end Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicDictionary
