import Alexander313.Wilken.SourceOneNativeSkSourceWordSupport

/-!
# Executing the original source-one initial sk and entire native loop

The original source-zero root is retained literally as the first entry.
Actual source-one eligibility stops immediately or executes the true first
next step. A false next flag appends its checked original-source return;
a true flag invokes the genuinely terminating native recurrence at the
real epsilon alpha context. Whole Path source-one provenance licenses
every direct finite source-zero return in the resulting chronological word.
No Native base-one parser, fuel, representation or mu-fidelity oracle.
This finite original-source producer does not assert Par invariance or a
global source-dictionary sk assignment. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkSourceWord

open Support
open SkSourcePathSupport (entryCode root_acceptedLow)

abbrev inputCheck := SkNextSearch.inputCheck

theorem inputCheck_primrec : Primrec₂ inputCheck := SkNextSearch.inputCheck_primrec

theorem inputCheck_exact (root cutoff : Nat) : inputCheck root cutoff = true ↔
    Mu.inputCheck root = true ∧ unionCheck cutoff = true := SkNextSearch.inputCheck_exact _ _

def afterFirst (p : Query) (out : SkNextSearch.Step) : Part (List Nat) := cond out.1
  ((NativeContext.PublicEpsilonUnboundedIota.SkIteration.execute
    ((alphaCode p.1, out.2), p.2)).map fun word => p.1 :: flatWord word)
  (Part.some [p.1, entryCode (alphaCode p.1) out.2])

theorem afterFirst_partrec : Partrec (fun p : Query × SkNextSearch.Step => afterFirst p.1 p.2) := by
  have hr : Primrec (fun p : Query × SkNextSearch.Step => p.1.1) := Primrec.fst.comp Primrec.fst
  have hc : Primrec (fun p : Query × SkNextSearch.Step => p.1.2) := Primrec.snd.comp Primrec.fst
  have hn : Primrec (fun p : Query × SkNextSearch.Step => p.2.2) := Primrec.snd.comp Primrec.snd
  have hi := ((alphaCode_primrec.comp hr).pair hn).pair hc
  have he := NativeContext.PublicEpsilonUnboundedIota.SkIteration.execute_partrec.comp hi.to_comp
  have hm : Computable₂ (fun p : Query × SkNextSearch.Step => fun word : Word =>
      p.1.1 :: flatWord word) :=
    (Primrec.list_cons.comp (hr.comp Primrec.fst) (flatWord_primrec.comp Primrec.snd)).to_comp.to₂
  have hd := SkSourcePathSupport.entryCode_primrec.comp (alphaCode_primrec.comp hr) hn
  have hs := Primrec.list_cons.comp hr (Primrec.list_cons.comp hd (Primrec.const []))
  exact Partrec.cond (Primrec.fst.comp Primrec.snd).to_comp
    (Partrec.map he hm) hs.to_comp.partrec

theorem afterFirst_returns (root cutoff : Nat) (out : SkNextSearch.Step)
    (ho : out ∈ SkNextSearch.execute (root, cutoff)) :
    ∃ codes, codes ∈ afterFirst (root, cutoff) out := by
  cases hh : out.1 with
  | false =>
    exact ⟨[root, entryCode (alphaCode root) out.2], by
      simp only [afterFirst, hh, Bool.cond_false, Part.mem_some_iff]⟩
  | true =>
    have hs := SkNextSearch.execute_spec root cutoff out ho
    have hc := ((inputCheck_exact root cutoff).mp hs.1).2
    have hn := (SkNextSearch.execute_continue root cutoff out ho hh).1
    have hi := (NativeContext.PublicEpsilonUnboundedIota.SkIteration.inputCheck_exact _ _ _).mpr ⟨hn, hc⟩
    obtain ⟨word, hw⟩ := NativeContext.PublicEpsilonUnboundedIota.SkIteration.execute_returns _ _ _ hi
    refine ⟨root :: flatWord word, ?_⟩
    rw [afterFirst, hh, Bool.cond_true]
    exact Part.mem_map _ hw

def execute (p : Query) : Part (List Nat) := cond (inputCheck p.1 p.2)
  (cond (eligible p.1 p.2) ((SkNextSearch.execute p).bind (afterFirst p))
    (Part.some [p.1])) Part.none

theorem execute_partrec : Partrec execute :=
  Partrec.cond inputCheck_primrec.to_comp
    (Partrec.cond eligible_primrec.to_comp
      (Partrec.bind SkNextSearch.execute_partrec afterFirst_partrec.to₂)
      (Primrec.list_cons.comp Primrec.fst (Primrec.const [])).to_comp.partrec) Partrec.none

theorem execute_domain (root cutoff : Nat) : (execute (root, cutoff)).Dom ↔ inputCheck root cutoff = true := by
  constructor
  · intro hd
    cases hi : inputCheck root cutoff with
    | true => rfl
    | false =>
      have hx : (Part.none : Part (List Nat)).Dom := by simpa only [execute, hi, Bool.cond_false] using hd
      exact False.elim (Part.not_none_dom hx)
  · intro hi
    cases he : eligible root cutoff with
    | false =>
      exact Part.dom_iff_mem.mpr ⟨[root], by
        simp only [execute, hi, he, Bool.cond_true, Bool.cond_false, Part.mem_some_iff]⟩
    | true =>
      obtain ⟨out, ho⟩ := SkNextSearch.execute_returns root cutoff hi
      obtain ⟨codes, hc⟩ := afterFirst_returns root cutoff out ho
      refine Part.dom_iff_mem.mpr ⟨codes, ?_⟩
      rw [execute, hi, he, Bool.cond_true]
      exact Part.mem_bind ho hc

theorem execute_returns (root cutoff : Nat) (hi : inputCheck root cutoff = true) :
    ∃ codes, codes ∈ execute (root, cutoff) := Part.dom_iff_mem.mp ((execute_domain root cutoff).mpr hi)

/-- The literal chronological output uses exactly the three genuine
alternatives: original mu below cutoff, emitted false next, or the entire
actual native Path after a true first next. -/
theorem execute_cases (root cutoff : Nat) (codes : List Nat) (hc : codes ∈ execute (root, cutoff)) :
    inputCheck root cutoff = true ∧
      ((Mu.sourceValue root < unionInterpretation cutoff ∧ codes = [root]) ∨
        (eligible root cutoff = true ∧ ∃ out, out ∈ SkNextSearch.execute (root, cutoff) ∧
          ((out.1 = false ∧ codes = [root, entryCode (alphaCode root) out.2]) ∨
            (out.1 = true ∧ ∃ word, word ∈ NativeContext.PublicEpsilonUnboundedIota.SkIteration.execute
              ((alphaCode root, out.2), cutoff) ∧ codes = root :: flatWord word)))) := by
  have hi := (execute_domain root cutoff).mp (Part.dom_iff_mem.mpr ⟨codes, hc⟩)
  have hs := (inputCheck_exact root cutoff).mp hi
  refine ⟨hi, ?_⟩
  cases he : eligible root cutoff with
  | false =>
    refine Or.inl ⟨(ineligible_exact root cutoff hs.1 hs.2).mp he, ?_⟩
    simpa only [execute, hi, he, Bool.cond_true, Bool.cond_false, Part.mem_some_iff] using hc
  | true =>
    rw [execute, hi, he, Bool.cond_true] at hc
    obtain ⟨out, ho, hout⟩ := Part.mem_bind_iff.mp hc
    refine Or.inr ⟨he, out, ho, ?_⟩
    cases hh : out.1 with
    | false =>
      refine Or.inl ⟨hh, ?_⟩
      simpa only [afterFirst, hh, Bool.cond_false, Part.mem_some_iff] using hout
    | true =>
      rw [afterFirst, hh, Bool.cond_true] at hout
      obtain ⟨word, hw, hcodes⟩ := (Part.mem_map_iff _).mp hout
      exact Or.inr ⟨hh, word, hw, hcodes.symm⟩

/-- Every entire executing source-one initialized word is original-source
Normal LOW, finite and nonempty, and retains the unchanged original root
as its literal first code. Whole Path fidelity licenses all later returns. -/
theorem execute_spec (root cutoff : Nat) (codes : List Nat) (hc : codes ∈ execute (root, cutoff)) :
    inputCheck root cutoff = true ∧ codes ≠ [] ∧
      (∃ tail, codes = root :: tail) ∧
      ∀ d ∈ codes, Theta.acceptedLowCode 0 d = true := by
  obtain ⟨hi, hs⟩ := execute_cases root cutoff codes hc
  have ha := ((inputCheck_exact root cutoff).mp hi).1
  have hr := root_acceptedLow root ha
  rcases hs with ⟨hb, rfl⟩ | ⟨he, out, ho, hs⟩
  · refine ⟨hi, List.cons_ne_nil _ _, ⟨[], rfl⟩, ?_⟩
    intro d hd
    rw [List.mem_singleton.mp hd]
    exact hr
  · rcases hs with ⟨hh, rfl⟩ | ⟨hh, word, hw, rfl⟩
    · refine ⟨hi, List.cons_ne_nil _ _, ⟨[entryCode (alphaCode root) out.2], rfl⟩, ?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hr
      · rw [List.mem_singleton.mp hd]
        exact (first_stopCode_spec root cutoff out ho).1
    · refine ⟨hi, List.cons_ne_nil _ _, ⟨flatWord word, rfl⟩, ?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hr
      · exact (first_flatWord_spec root cutoff out ho hh word hw).1 d hd

theorem execute_stop_values (root cutoff : Nat) (codes : List Nat) (hc : codes ∈ execute (root, cutoff))
    (out : SkNextSearch.Step) (ho : out ∈ SkNextSearch.execute (root, cutoff))
    (he : codes = [root, entryCode (alphaCode root) out.2]) :
    codes.map (interpretation 0) = [interpretation 0 root,
      SkNextStepSupport.nextValue root (unionInterpretation cutoff)] := by
  rw [he]
  simp only [List.map_cons, List.map_nil, (first_stopCode_spec root cutoff out ho).2,
    (SkNextSearch.execute_spec root cutoff out ho).2.2.2.1]

theorem execute_continued_values (root cutoff : Nat) (out : SkNextSearch.Step)
    (ho : out ∈ SkNextSearch.execute (root, cutoff)) (hh : out.1 = true)
    (word : Word) (hw : word ∈ NativeContext.PublicEpsilonUnboundedIota.SkIteration.execute
      ((alphaCode root, out.2), cutoff)) :
    (root :: flatWord word).map (interpretation 0) = interpretation 0 root ::
      word.map (fun entry => NativeContext.interpretation entry.1 entry.2) := by
  simp only [List.map_cons, (first_flatWord_spec root cutoff out ho hh word hw).2]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkSourceWord
