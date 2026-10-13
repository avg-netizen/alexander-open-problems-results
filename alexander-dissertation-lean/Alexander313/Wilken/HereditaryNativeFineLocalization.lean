import Alexander313.Wilken.HereditaryNativeSourceZeta
import Alexander313.Wilken.HereditaryFineLocalizationOrder

/-!
# Executing fine localization in the same positive public epsilon context

Original native weak-normal theta-zero roots undergo the actual public payload
return. The real public fine search is executed directly, including its proved
zero-step base case. Raw original theta-zero roots retain the actual proper-root
guard and use the real public normalizer after return. No equality of independently
executed native/public normalizers is required.

Every searched public node has original low admission. Its real endpoint bound
licenses canonical emission, bounded return and translation to the SAME native
context. The output word has precisely the values of the genuine public FinePath,
so its endpoints, strictness, canonical-choice invariance and source2.40 follow
from those actual paths. Its native spellings are not asserted to follow an
independently constructed native fine-predecessor recurrence. Arbitrary temporary
epsilon bases, Par/support/spelling laws and a PR global search bound are absent.
All proof candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.FineLocalization

open NativePublicBridge (contextCode contextCode_value)

def inputCheck (s c : Nat) : Bool := SourceZeta.inputCheck s c

theorem inputCheck_primrec : Primrec₂ inputCheck := SourceZeta.inputCheck_primrec

theorem inputCheck_exact (s c : Nat) : inputCheck s c = true ↔
    ∃ a : RelativeTerm Nat, c = (.theta 0 a).code ∧ check (contextCode s) (.theta 0 a) = true ∧
      Comparison.Normal (contextCode s) (.theta 0 a) := SourceZeta.inputCheck_exact s c

def publicCode (s c : Nat) : Nat := NativePublicReturn.returnedCode s c

theorem publicCode_primrec : Primrec₂ publicCode := NativePublicReturn.returnedCode_primrec

theorem publicCode_node (s c : Nat) (hc : inputCheck s c = true) :
    Localization.Node (s + 1) (publicCode s c) :=
  (Hereditary.SourceZeta.inputCheck_exact _ _).mp (SourceZeta.public_normal_input s c hc)

theorem publicCode_value (s c : Nat) (hc : inputCheck s c = true) :
    Localization.value (s + 1) (publicCode s c) = interpretation (contextCode s) c :=
  SourceZeta.publicCode_value s c (SourceZeta.normal_raw_input s c hc)

/-- The raw domain is original literal theta-zero admission AND actual value
strictly above the base. The real public raw guard is computed, not assumed. -/
def rawInputCheck (s c : Nat) : Bool := SourceZeta.rawInputCheck s c &&
  FinePredecessor.rawInputCheck (s + 1) (publicCode s c)

theorem rawInputCheck_primrec : Primrec₂ rawInputCheck :=
  (Primrec.and.comp SourceZeta.rawInputCheck_primrec
    (FinePredecessor.rawInputCheck_primrec.comp (Primrec.succ.comp Primrec.fst) publicCode_primrec)).to₂

theorem rawInputCheck_exact (s c : Nat) : rawInputCheck s c = true ↔
    (∃ a : RelativeTerm Nat, c = (.theta 0 a).code ∧ check (contextCode s) (.theta 0 a) = true) ∧
      base (contextCode s) < interpretation (contextCode s) c := by
  constructor
  · intro hc
    obtain ⟨hn, hp⟩ := Bool.and_eq_true.mp hc
    have hs := (FinePredecessor.rawInputCheck_exact _ _).mp hp
    exact ⟨(SourceZeta.rawInputCheck_exact s c).mp hn, by
      simpa only [contextCode_value, SourceZeta.publicCode_value s c hn] using hs.2⟩
  · rintro ⟨hc, hb⟩
    have hn := (SourceZeta.rawInputCheck_exact s c).mpr hc
    have hp := (Hereditary.SourceZeta.rawInputCheck_exact _ _).mp (SourceZeta.public_raw_input s c hn)
    refine Bool.and_eq_true.mpr ⟨hn, (FinePredecessor.rawInputCheck_exact _ _).mpr ⟨hp, ?_⟩⟩
    simpa only [contextCode_value, SourceZeta.publicCode_value s c hn] using hb

def rawPublicCode (s c : Nat) : Nat := NativePublicReturn.rawReturnCode s c

theorem rawPublicCode_primrec : Primrec₂ rawPublicCode := NativePublicReturn.rawReturnCode_primrec

theorem rawPublicCode_node (s c : Nat) (hc : rawInputCheck s c = true) :
    Localization.Node (s + 1) (rawPublicCode s c) :=
  ((FinePredecessor.inputCheck_exact _ _).mp
    (FinePredecessor.raw_normalized_input _ _ (Bool.and_eq_true.mp hc).2)).1

theorem rawPublicCode_value (s c : Nat) (hc : rawInputCheck s c = true) :
    Localization.value (s + 1) (rawPublicCode s c) = interpretation (contextCode s) c :=
  (NativePublicReturn.rawReturnCode_spec s c (Bool.and_eq_true.mp (Bool.and_eq_true.mp hc).1).1).2

/-- Each actual public node supplies its own return bound; no extra caller
bound is part of the input domain. -/
theorem publicNode_bound (s d : Nat) (hd : Localization.Node (s + 1) d) :
    Localization.value (s + 1) d < finiteBase (s + 2) := by
  have hb := (lt_nextBase_iff_code (s + 1) _).mpr ⟨d, Localization.node_low (s + 1) d hd, rfl⟩
  simpa only [Nat.add_assoc] using hb

def nodeCode (s d : Nat) : Nat := SourceZeta.emit s (Localization.emit (s + 1) d)

theorem nodeCode_primrec : Primrec₂ nodeCode :=
  (SourceZeta.emit_primrec.comp Primrec.fst
    (Localization.emit_primrec.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)).to₂

theorem nodeCode_spec (s d : Nat) (hd : Localization.Node (s + 1) d) :
    Comparison.acceptedCode (contextCode s) (nodeCode s d) = true ∧
      lowCheckCode (contextCode s) (nodeCode s d) = true ∧
      interpretation (contextCode s) (nodeCode s d) = Localization.value (s + 1) d := by
  have he := Localization.emit_spec (s + 1) d hd
  have hs := SourceZeta.emit_spec s _ he.1 (he.2.symm ▸ publicNode_bound s d hd)
  exact ⟨hs.1, hs.2.1, hs.2.2.trans he.2⟩

theorem nodeCode_eq_of_value_eq (s d e : Nat)
    (hd : Localization.Node (s + 1) d) (he : Localization.Node (s + 1) e)
    (hv : Localization.value (s + 1) d = Localization.value (s + 1) e) : nodeCode s d = nodeCode s e := by
  have hs := Localization.emit_spec (s + 1) d hd
  have ht := Localization.emit_spec (s + 1) e he
  exact congrArg (SourceZeta.emit s) (Canonical.check_value_injective _ _ hs.1 ht.1 (hs.2.trans (hv.trans ht.2.symm)))

def word (s root n : Nat) : List Nat := (Hereditary.FineLocalization.word (s + 1) root n).map (nodeCode s)

theorem word_primrec : Primrec (fun p : (Nat × Nat) × Nat => word p.1.1 p.1.2 p.2) := by
  have hp := Hereditary.FineLocalization.word_primrec.comp
    (((Primrec.succ.comp (Primrec.fst.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  have hm : Primrec₂ (fun p : (Nat × Nat) × Nat => fun d : Nat => nodeCode p.1.1 d) :=
    (nodeCode_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂
  exact Primrec.list_map hp hm

def run (s root : Nat) : Part Nat := (Hereditary.FineLocalization.search (Nat.pair (s + 1) root)).map
  (fun n => Encodable.encode (word s root n))

theorem run_partrec : Partrec₂ run := by
  have hs := Hereditary.FineLocalization.search_partrec.comp
    (Primrec₂.natPair.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to_comp
  exact (hs.map (Primrec.encode.comp word_primrec).to_comp.to₂).to₂

theorem run_domain (s root : Nat) (hr : Localization.Node (s + 1) root) : (run s root).Dom :=
  Hereditary.FineLocalization.search_domain (s + 1) root hr

theorem run_source (s root output : Nat) (hr : Localization.Node (s + 1) root)
    (ho : output ∈ run s root) :
    ∃ n, n ∈ Hereditary.FineLocalization.search (Nat.pair (s + 1) root) ∧
      output = Encodable.encode (word s root n) ∧
      Hereditary.FineLocalization.FinePath (s + 1) root (Hereditary.FineLocalization.word (s + 1) root n) := by
  obtain ⟨n, hn, he⟩ := (Part.mem_map_iff _).mp ho
  exact ⟨n, hn, he.symm, Hereditary.FineLocalization.run_path (s + 1) root n hr
    (Hereditary.FineLocalization.search_halt _ _ _ hn) (Hereditary.FineLocalization.search_before _ _ _ hn)⟩

def fineLocalization (s c : Nat) : Part Nat := cond (inputCheck s c) (run s (publicCode s c)) Part.none

theorem fineLocalization_partrec : Partrec₂ fineLocalization :=
  (Partrec.cond inputCheck_primrec.to_comp
    (run_partrec.comp Computable.fst publicCode_primrec.to_comp) Partrec.none).to₂

theorem fineLocalization_domain (s c : Nat) : (fineLocalization s c).Dom ↔ inputCheck s c = true := by
  cases hc : inputCheck s c with
  | false => simp [fineLocalization, hc, Part.none]
  | true =>
    simp only [fineLocalization, hc, Bool.cond_true]
    exact ⟨fun _ => rfl, fun _ => run_domain s _ (publicCode_node s c hc)⟩

def rawFineLocalization (s c : Nat) : Part Nat := cond (rawInputCheck s c) (run s (rawPublicCode s c)) Part.none

theorem rawFineLocalization_partrec : Partrec₂ rawFineLocalization :=
  (Partrec.cond rawInputCheck_primrec.to_comp
    (run_partrec.comp Computable.fst rawPublicCode_primrec.to_comp) Partrec.none).to₂

theorem rawFineLocalization_domain (s c : Nat) : (rawFineLocalization s c).Dom ↔ rawInputCheck s c = true := by
  cases hc : rawInputCheck s c with
  | false => simp [rawFineLocalization, hc, Part.none]
  | true =>
    simp only [rawFineLocalization, hc, Bool.cond_true]
    exact ⟨fun _ => rfl, fun _ => run_domain s _ (rawPublicCode_node s c hc)⟩

def decodedWord (output : Nat) : List Nat := Hereditary.FineLocalization.Invariance.decodedWord output

theorem decodedWord_primrec : Primrec decodedWord := Hereditary.FineLocalization.Invariance.decodedWord_primrec

@[simp] theorem decodedWord_encode (path : List Nat) : decodedWord (Encodable.encode path) = path :=
  Hereditary.FineLocalization.Invariance.decodedWord_encode path

noncomputable def outputValues (s output : Nat) : List Ordinal.{0} := (decodedWord output).map (interpretation (contextCode s))

/-- The output is the actual canonical-choice map of a genuine public path.
This deliberately distinguishes value recurrence from native spelling recurrence. -/
def OutputSpec (s root output : Nat) : Prop := ∃ path : List Nat,
  Hereditary.FineLocalization.FinePath (s + 1) root path ∧
    output = Encodable.encode (path.map (nodeCode s))

theorem run_outputSpec (s root output : Nat) (hr : Localization.Node (s + 1) root)
    (ho : output ∈ run s root) : OutputSpec s root output := by
  obtain ⟨n, hn, he, hp⟩ := run_source s root output hr ho
  exact ⟨Hereditary.FineLocalization.word (s + 1) root n, hp, he⟩

theorem fineLocalization_source (s c output : Nat) (ho : output ∈ fineLocalization s c) :
    inputCheck s c = true ∧ OutputSpec s (publicCode s c) output := by
  have hc := (fineLocalization_domain s c).mp (Part.dom_iff_mem.mpr ⟨output, ho⟩)
  exact ⟨hc, run_outputSpec s _ output (publicCode_node s c hc)
    (by simpa only [fineLocalization, hc, Bool.cond_true] using ho)⟩

theorem rawFineLocalization_source (s c output : Nat) (ho : output ∈ rawFineLocalization s c) :
    rawInputCheck s c = true ∧ OutputSpec s (rawPublicCode s c) output := by
  have hc := (rawFineLocalization_domain s c).mp (Part.dom_iff_mem.mpr ⟨output, ho⟩)
  exact ⟨hc, run_outputSpec s _ output (rawPublicCode_node s c hc)
    (by simpa only [rawFineLocalization, hc, Bool.cond_true] using ho)⟩

theorem OutputSpec.values {s root output : Nat} (hs : OutputSpec s root output) :
    ∃ path, Hereditary.FineLocalization.FinePath (s + 1) root path ∧
      outputValues s output = path.map (Localization.value (s + 1)) := by
  obtain ⟨path, hp, he⟩ := hs
  refine ⟨path, hp, ?_⟩
  simp only [outputValues, he, decodedWord_encode, List.map_map]
  apply List.map_congr_left
  intro d hd
  exact (nodeCode_spec s d (hp.nodes d hd)).2.2

theorem OutputSpec.nodes {s root output : Nat} (hs : OutputSpec s root output) :
    ∀ d ∈ decodedWord output, Comparison.acceptedCode (contextCode s) d = true ∧
      lowCheckCode (contextCode s) d = true := by
  obtain ⟨path, hp, he⟩ := hs
  simp only [he, decodedWord_encode]
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  have ht := nodeCode_spec s e (hp.nodes e he)
  exact ⟨ht.1, ht.2.1⟩

theorem OutputSpec.strict {s root output : Nat} (hs : OutputSpec s root output) :
    (outputValues s output).Pairwise (· < ·) := by
  obtain ⟨path, hp, he⟩ := hs.values
  rw [he]
  exact hp.strict

theorem OutputSpec.endpoints {s root output : Nat} (hs : OutputSpec s root output) :
    ∃ middle, outputValues s output = finiteBase (s + 1) :: middle ∧
      ∃ pre, outputValues s output = pre ++ [Localization.value (s + 1) root] := by
  obtain ⟨path, hp, he⟩ := hs.values
  obtain ⟨b, tail, ht, hb⟩ := hp.start
  obtain ⟨pre, hend⟩ := hp.end
  refine ⟨tail.map (Localization.value (s + 1)), ?_, pre.map (Localization.value (s + 1)), ?_⟩
  · rw [he, ht, List.map_cons, hb]
  · rw [he, hend, List.map_append, List.map_cons, List.map_nil]

theorem OutputSpec.output_eq {s root other output second : Nat}
    (hs : OutputSpec s root output) (ht : OutputSpec s other second)
    (hv : Localization.value (s + 1) root = Localization.value (s + 1) other) : output = second := by
  obtain ⟨path, hp, he⟩ := hs
  obtain ⟨rest, hq, hf⟩ := ht
  have hcanon := Hereditary.FineLocalization.Invariance.FinePath.emissions_eq hp hq hv
  have hmap : path.map (nodeCode s) = rest.map (nodeCode s) := by
    simpa only [nodeCode, List.map_map] using congrArg (List.map (SourceZeta.emit s)) hcanon
  exact he.trans ((congrArg Encodable.encode hmap).trans hf.symm)

theorem OutputSpec.lex_iff {s root other output second : Nat}
    (hs : OutputSpec s root output) (ht : OutputSpec s other second) :
    List.Lex (· < ·) (outputValues s output) (outputValues s second) ↔
      Localization.value (s + 1) root < Localization.value (s + 1) other := by
  obtain ⟨path, hp, he⟩ := hs.values
  obtain ⟨rest, hq, hf⟩ := ht.values
  rw [he, hf]
  exact Hereditary.FineLocalization.Order.FinePath.values_lex_iff hp hq

theorem fineLocalization_invariant (s c d output second : Nat)
    (ho : output ∈ fineLocalization s c) (hv : second ∈ fineLocalization s d)
    (he : interpretation (contextCode s) c = interpretation (contextCode s) d) : output = second := by
  have hp := fineLocalization_source s c output ho
  have hq := fineLocalization_source s d second hv
  exact hp.2.output_eq hq.2 ((publicCode_value s c hp.1).trans (he.trans (publicCode_value s d hq.1).symm))

theorem rawFineLocalization_invariant (s c d output second : Nat)
    (ho : output ∈ rawFineLocalization s c) (hv : second ∈ rawFineLocalization s d)
    (he : interpretation (contextCode s) c = interpretation (contextCode s) d) : output = second := by
  have hp := rawFineLocalization_source s c output ho
  have hq := rawFineLocalization_source s d second hv
  exact hp.2.output_eq hq.2 ((rawPublicCode_value s c hp.1).trans (he.trans (rawPublicCode_value s d hq.1).symm))

theorem fineLocalization_lex_iff (s c d output second : Nat)
    (ho : output ∈ fineLocalization s c) (hv : second ∈ fineLocalization s d) :
    List.Lex (· < ·) (outputValues s output) (outputValues s second) ↔
      interpretation (contextCode s) c < interpretation (contextCode s) d := by
  have hp := fineLocalization_source s c output ho
  have hq := fineLocalization_source s d second hv
  simpa only [publicCode_value s c hp.1, publicCode_value s d hq.1] using hp.2.lex_iff hq.2

theorem rawFineLocalization_lex_iff (s c d output second : Nat)
    (ho : output ∈ rawFineLocalization s c) (hv : second ∈ rawFineLocalization s d) :
    List.Lex (· < ·) (outputValues s output) (outputValues s second) ↔
      interpretation (contextCode s) c < interpretation (contextCode s) d := by
  have hp := rawFineLocalization_source s c output ho
  have hq := rawFineLocalization_source s d second hv
  simpa only [rawPublicCode_value s c hp.1, rawPublicCode_value s d hq.1] using hp.2.lex_iff hq.2

theorem fineLocalization_base (s c : Nat) (hc : inputCheck s c = true)
    (hb : interpretation (contextCode s) c = base (contextCode s)) :
    Encodable.encode [nodeCode s (publicCode s c)] ∈ fineLocalization s c := by
  have hn := publicCode_node s c hc
  have hv : Localization.value (s + 1) (publicCode s c) = finiteBase (s + 1) :=
    (publicCode_value s c hc).trans (hb.trans (contextCode_value s))
  have hh := (Hereditary.FineLocalization.haltCheck_exact _ _ 0 hn).mpr hv
  have hzero : 0 ∈ Hereditary.FineLocalization.search (Nat.pair (s + 1) (publicCode s c)) := by
    rw [Hereditary.FineLocalization.search, Nat.mem_rfind]
    exact ⟨by simpa only [Nat.unpair_pair, Part.mem_some_iff] using hh.symm,
      fun {m} hm => False.elim (Nat.not_lt_zero m hm)⟩
  simp only [fineLocalization, hc, Bool.cond_true, run]
  exact (Part.mem_map_iff _).mpr ⟨0, hzero, rfl⟩

theorem rawInputCheck_base_false (s c : Nat)
    (hb : interpretation (contextCode s) c = base (contextCode s)) : rawInputCheck s c = false := by
  cases h : rawInputCheck s c with
  | false => rfl
  | true =>
    have hs := (rawInputCheck_exact s c).mp h
    exact False.elim ((ne_of_lt hs.2) hb.symm)

theorem fineLocalization_base_values (s c output : Nat) (ho : output ∈ fineLocalization s c)
    (hb : interpretation (contextCode s) c = base (contextCode s)) :
    outputValues s output = [base (contextCode s)] := by
  have hc := (fineLocalization_source s c output ho).1
  have he := Part.mem_unique ho (fineLocalization_base s c hc hb)
  have hn := nodeCode_spec s _ (publicCode_node s c hc)
  simp only [outputValues, he, decodedWord_encode, List.map_cons, List.map_nil,
    hn.2.2, publicCode_value s c hc, hb]

theorem fineLocalization_returns (s c : Nat) (hc : inputCheck s c = true) :
    ∃! output, output ∈ fineLocalization s c := by
  obtain ⟨output, ho⟩ := Part.dom_iff_mem.mp ((fineLocalization_domain s c).mpr hc)
  exact ⟨output, ho, fun other ht => Part.mem_unique ht ho⟩

theorem rawFineLocalization_returns (s c : Nat) (hc : rawInputCheck s c = true) :
    ∃! output, output ∈ rawFineLocalization s c := by
  obtain ⟨output, ho⟩ := Part.dom_iff_mem.mp ((rawFineLocalization_domain s c).mpr hc)
  exact ⟨output, ho, fun other ht => Part.mem_unique ht ho⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.FineLocalization
