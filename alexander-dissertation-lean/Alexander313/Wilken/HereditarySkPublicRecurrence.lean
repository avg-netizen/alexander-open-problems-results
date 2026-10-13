import Alexander313.Wilken.HereditarySkPublicRecurrenceSupport

/-!
# Whole executed public sk carries its actual mu recurrence

The real selected-source public execution has canonical output. Every
source entry is genuinely LOW in that retained original finite context,
so its canonical emission is the actual public output spelling. The
original maximal path thereby becomes a public chronological path whose
mu queries are independently executed by the concrete public dictionary.
The literal original canonical initial code and both maximal stops are
retained; no recurrence, source-selection or mu oracle is supplied.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicRecurrence

open MuPublicDictionary.Agreement

theorem native_word_spec (s : Nat) (codes : List Nat)
    (hl : ∀ d ∈ codes, NativeContext.lowCheckCode (NativePublicBridge.contextCode s) d = true) :
    (∀ c ∈ codes.map (positivePublicCode s), Canonical.check c = true) ∧
      (codes.map (positivePublicCode s)).map unionInterpretation =
        codes.map (NativeContext.interpretation (NativePublicBridge.contextCode s)) := by
  constructor
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (NativeContext.UniformPublicReturn.publicCode_spec _ d
      ((NativeContext.UniformPublicReturn.inputCheck_exact _ d).mpr (hl d hd))).1
  · rw [List.map_map]
    exact List.map_congr_left (fun d hd =>
      (NativeContext.UniformPublicReturn.publicCode_spec _ d
        ((NativeContext.UniformPublicReturn.inputCheck_exact _ d).mpr (hl d hd))).2)

theorem source_one_word_spec (codes : List Nat)
    (hl : ∀ d ∈ codes, lowCheckCode 0 d = true) :
    (∀ c ∈ codes.map sourceOnePublicCode, Canonical.check c = true) ∧
      (codes.map sourceOnePublicCode).map unionInterpretation = codes.map (interpretation 0) := by
  constructor
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (SourceOneIota.SourceTrackingRaw.Support.publicCode_spec d (hl d hd)).1
  · rw [List.map_map]
    exact List.map_congr_left (fun d hd =>
      (SourceOneIota.SourceTrackingRaw.Support.publicCode_spec d (hl d hd)).2)

/-- Actual independent public execution alone derives the complete public
mu-query recurrence and both genuine maximal stopping alternatives. -/
theorem execute_path (gamma cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ SkPublicDictionary.execute (gamma, cutoff)) : Path cutoff codes := by
  have hs := SkPublicDictionary.execute_spec gamma cutoff codes ho
  rcases hs.2.2 with ⟨hlevel, source, hsource, hp, hv, a, xs, hhead, hvalue⟩ |
      ⟨hlevel, source, hsource, hp, hv, a, xs, hhead, hvalue⟩
  · have hw := source_one_word_spec source (source_one_path_low hp)
    have he := NativeContext.PublicEpsilonUnboundedIota.SkPublicValueInvariance.canonical_words_eq
      codes (source.map sourceOnePublicCode) hs.2.1 hw.1 (hv.trans hw.2.symm)
    rw [he]
    exact source_one_path cutoff hp
  · let s := PublicEpsilonSourceDictionary.sourceIndex gamma
    have hp' : NativeContext.PublicEpsilonUnboundedIota.SkSourceRecurrence.SourcePath
        (NativePublicBridge.contextCode s) cutoff source := by
      simpa only [SkPublicDictionary.Support.nativeQuery, s] using hp
    have hw := native_word_spec s source (native_path_low hp')
    have hv' : codes.map unionInterpretation =
        source.map (NativeContext.interpretation (NativePublicBridge.contextCode s)) := by
      simpa only [SkPublicDictionary.Support.nativeQuery, s] using hv
    have he := NativeContext.PublicEpsilonUnboundedIota.SkPublicValueInvariance.canonical_words_eq
      codes (source.map (positivePublicCode s)) hs.2.1 hw.1 (hv'.trans hw.2.symm)
    rw [he]
    exact native_path s cutoff hp'

/-- Canonical value injection preserves the actual input code itself,
not merely an unrelated equal-valued first entry. -/
theorem execute_initial (gamma cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ SkPublicDictionary.execute (gamma, cutoff)) :
    ∃ xs, codes = gamma :: xs ∧ 1 < unionInterpretation gamma := by
  have hs := SkPublicDictionary.execute_spec gamma cutoff codes ho
  have hg := (PublicEpsilonSourceDictionary.inputCheck_exact gamma).mp
    ((SkPublicDictionary.Support.inputCheck_exact gamma cutoff).mp hs.1).1
  have hpos := EpsilonOffsets.epsilon_one_lt hg.2
  rcases hs.2.2 with ⟨hl, source, hsource, hp, hv, a, xs, hhead, hvalue⟩ |
      ⟨hl, source, hsource, hp, hv, a, xs, hhead, hvalue⟩ <;>
    cases codes with
    | nil =>
      rw [hhead, List.map_nil, List.map_cons] at hv
      exact False.elim (List.cons_ne_nil _ _ hv.symm)
    | cons c cs =>
      rw [hhead, List.map_cons] at hv
      have he : c = gamma := Canonical.check_value_injective c gamma
        (hs.2.1 c List.mem_cons_self) hg.1 ((List.cons.inj hv).1.trans hvalue)
      exact ⟨cs, by rw [he], hpos⟩

theorem execute_spec (gamma cutoff : Nat) (codes : List Nat)
    (ho : codes ∈ SkPublicDictionary.execute (gamma, cutoff)) :
    SkPublicDictionary.Support.inputCheck gamma cutoff = true ∧ Path cutoff codes ∧
      (∀ c ∈ codes, Canonical.check c = true) ∧
        ∃ xs, codes = gamma :: xs ∧ 1 < unionInterpretation gamma := by
  have hs := SkPublicDictionary.execute_spec gamma cutoff codes ho
  exact ⟨hs.1, execute_path gamma cutoff codes ho, hs.2.1, execute_initial gamma cutoff codes ho⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicRecurrence
