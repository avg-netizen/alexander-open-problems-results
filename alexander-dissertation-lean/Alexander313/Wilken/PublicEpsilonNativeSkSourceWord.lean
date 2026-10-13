import Alexander313.Wilken.PublicEpsilonNativeSkSourceWordSupport

/-!
# Executing one-original-source sk words and canonical public outputs

The native recurrence executes first. Every chronological entry then runs
the genuine original-q LOW return search, whose callers follow from the
whole-Path provenance proof. The output is finite checked Normal LOW
syntax at that SAME original source, with exactly the native ordinal-value
word. Canonical public outputs retain the same chronology. This establishes
executing flattening and its exact original domain, not a Par invariant,
spelling-independent assignment or full tracking/evaluation theorem.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkSourceWord

open Support

def execute (p : SkNextSearch.Support.Query) : Part (List Nat) :=
  (SkIteration.execute p).bind fun word => loop (p.1.1, (word, []))

theorem execute_partrec : Partrec execute := by
  have hl : Partrec₂ (fun p : SkNextSearch.Support.Query => fun word : Word =>
      loop (p.1.1, (word, []))) :=
    (loop_partrec.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.pair (Primrec.const []))).to_comp).to₂
  exact Partrec.bind SkIteration.execute_partrec hl

theorem execute_domain (q root cutoff : Nat) : (execute ((q, root), cutoff)).Dom ↔
    SkIteration.inputCheck q root cutoff = true := by
  constructor
  · intro hd
    obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨word, hw, hs⟩ := Part.mem_bind_iff.mp ho
    exact (SkIteration.execute_domain q root cutoff).mp (Part.dom_iff_mem.mpr ⟨word, hw⟩)
  · intro hi
    obtain ⟨word, hw⟩ := SkIteration.execute_returns q root cutoff hi
    obtain ⟨out, ho⟩ := loop_returns q word [] (SkSourcePathSupport.execute_entry_search q root cutoff word hw)
    exact Part.dom_iff_mem.mpr ⟨out, Part.mem_bind hw ho⟩

theorem execute_returns (q root cutoff : Nat) (hi : SkIteration.inputCheck q root cutoff = true) :
    ∃ out, out ∈ execute ((q, root), cutoff) := Part.dom_iff_mem.mp ((execute_domain q root cutoff).mpr hi)

/-- Actual original native guard alone derives every search caller and
the entire checked Normal SAME-source chronological output relation. -/
theorem execute_relation (q root cutoff : Nat) (codes : List Nat)
    (hc : codes ∈ execute ((q, root), cutoff)) :
    SkIteration.inputCheck q root cutoff = true ∧ ∃ word,
      word ∈ SkIteration.execute ((q, root), cutoff) ∧
        SkIteration.Path cutoff (q, root) word ∧ List.Forall₂ (EntryMatches q) word codes := by
  obtain ⟨word, hw, ho⟩ := Part.mem_bind_iff.mp hc
  have hs := SkIteration.execute_spec q root cutoff word hw
  obtain ⟨tail, he, hr⟩ := loop_relation (q, (word, [])) codes ho
    (fun entry hm => (hs.2.2.2 entry hm).1)
  have hcodes : codes = tail := by simpa only [List.nil_append] using he
  subst tail
  exact ⟨hs.1, word, hw, hs.2.1, hr⟩

theorem execute_spec (q root cutoff : Nat) (codes : List Nat)
    (hc : codes ∈ execute ((q, root), cutoff)) :
    codes ≠ [] ∧ (∀ d ∈ codes, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true) ∧
      ∃ word, word ∈ SkIteration.execute ((q, root), cutoff) ∧
        codes.map (interpretation q) = word.map (fun entry => interpretation entry.1 entry.2) := by
  obtain ⟨hi, word, hw, hp, hr⟩ := execute_relation q root cutoff codes hc
  have hv := relation_values q hr
  have hne : codes ≠ [] := by
    intro he
    have hn : word = [] := List.map_eq_nil_iff.mp (by simpa only [he, List.map_nil] using hv.symm)
    exact hp.nonempty hn
  exact ⟨hne, relation_checked q hr, word, hw, hv⟩

def publicWord (word : Word) : List Nat := word.map fun entry =>
  UniformPublicReturn.publicCode entry.1 entry.2

theorem publicWord_primrec : Primrec publicWord := by
  have hentry : Primrec₂ (fun word : Word => fun entry : Context =>
      UniformPublicReturn.publicCode entry.1 entry.2) :=
    (UniformPublicReturn.publicCode_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_map Primrec.id hentry

def executePublic (p : SkNextSearch.Support.Query) : Part (List Nat) :=
  (SkIteration.execute p).map publicWord

theorem executePublic_partrec : Partrec executePublic :=
  Partrec.map SkIteration.execute_partrec (publicWord_primrec.comp Primrec.snd).to_comp.to₂

theorem executePublic_domain (q root cutoff : Nat) : (executePublic ((q, root), cutoff)).Dom ↔
    SkIteration.inputCheck q root cutoff = true := by
  change ((SkIteration.execute ((q, root), cutoff)).map publicWord).Dom ↔ _
  exact SkIteration.execute_domain q root cutoff

/-- The concrete canonical public output is exactly the same native value
word and carries a canonical check for every chronological entry. -/
theorem executePublic_spec (q root cutoff : Nat) (codes : List Nat)
    (hc : codes ∈ executePublic ((q, root), cutoff)) :
    SkIteration.inputCheck q root cutoff = true ∧ (∀ d ∈ codes, Canonical.check d = true) ∧
      ∃ word, word ∈ SkIteration.execute ((q, root), cutoff) ∧
        codes.map unionInterpretation = word.map (fun entry => interpretation entry.1 entry.2) := by
  obtain ⟨word, hw, rfl⟩ := (Part.mem_map_iff publicWord).mp hc
  have hs := SkIteration.execute_spec q root cutoff word hw
  have hp (entry : Context) (he : entry ∈ word) := UniformPublicReturn.publicCode_spec entry.1 entry.2
    ((UniformPublicReturn.inputCheck_exact _ _).mpr (hs.2.2.2 entry he).1)
  refine ⟨hs.1, ?_, word, hw, ?_⟩
  · intro d hd
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hd
    exact (hp entry he).1
  · rw [publicWord, List.map_map]
    apply List.map_congr_left
    intro entry he
    exact (hp entry he).2

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkSourceWord
