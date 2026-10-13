import Alexander313.Wilken.PublicEpsilonNativeSkNextSearch
import Alexander313.Wilken.PublicEpsilonNativeTrackingSequencesSupport

/-!
# Actual native sk eligibility and partial while-loop transition

The current root and source context remain literal. The original public
cutoff is compared with actual canonical mu before truncation. A failed
eligibility test stops at the current root; otherwise the executing next
step appends its exact context/code pair. Only a genuinely epsilon next
value strictly above the current root enters another iteration. Its actual
written height strictly decreases. No fuel, halt, representative, endpoint,
plus or Par oracle is supplied. Original source-one initialization remains
a separate dictionary. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkIteration.Support

abbrev Word := List Context
abbrev Input := Nat × (Context × Word)

def eligible (cutoff q root : Nat) : Bool := SkNextSearch.inputCheck q root cutoff &&
  !(Canonical.less (SkNextSearch.Support.muPublicCode q root) (Canonical.canonicalize cutoff))

theorem eligible_primrec : Primrec (fun p : Nat × Context => eligible p.1 p.2.1 p.2.2) := by
  have hi := SkNextSearch.inputCheck_primrec.comp (Primrec.snd.pair Primrec.fst)
  have hm := Primrec.comp SkNextSearch.Support.muPublicCode_primrec Primrec.snd
  have hc := Canonical.Effective.canonicalize_primrec.comp Primrec.fst
  exact Primrec.and.comp hi (Primrec.not.comp (Canonical.Effective.less_primrec.comp hm hc))

theorem eligible_exact (cutoff q root : Nat) : eligible cutoff q root = true ↔
    Mu.inputCheck q root = true ∧ unionCheck cutoff = true ∧
      unionInterpretation cutoff ≤ Mu.sourceValue q root := by
  constructor
  · intro he
    obtain ⟨hi, hl⟩ := Bool.and_eq_true.mp he
    obtain ⟨ha, hc⟩ := (SkNextSearch.inputCheck_exact q root cutoff).mp hi
    have hm := SkNextSearch.Support.muPublicCode_spec q root ha
    have hb := SourceTrackingSequences.Support.canonical_not_less_exact _ _ hm.1
      (Canonical.canonicalize_check cutoff hc)
    exact ⟨ha, hc, by simpa only [hm.2, Canonical.canonicalize_value cutoff hc] using hb.mp hl⟩
  · rintro ⟨ha, hc, hle⟩
    have hm := SkNextSearch.Support.muPublicCode_spec q root ha
    refine Bool.and_eq_true.mpr ⟨(SkNextSearch.inputCheck_exact q root cutoff).mpr ⟨ha, hc⟩, ?_⟩
    apply (SourceTrackingSequences.Support.canonical_not_less_exact _ _ hm.1
      (Canonical.canonicalize_check cutoff hc)).mpr
    simpa only [hm.2, Canonical.canonicalize_value cutoff hc] using hle

theorem ineligible_exact (cutoff q root : Nat) (ha : Mu.inputCheck q root = true)
    (hc : unionCheck cutoff = true) : eligible cutoff q root = false ↔
      Mu.sourceValue q root < unionInterpretation cutoff := by
  constructor
  · intro he
    apply lt_of_not_ge
    intro hle
    have ht := (eligible_exact cutoff q root).mpr ⟨ha, hc, hle⟩
    rw [he] at ht
    cases ht
  · intro hlt
    apply Bool.eq_false_of_not_eq_true
    intro he
    exact hlt.not_ge ((eligible_exact cutoff q root).mp he).2.2

def advance (p : Input) (out : SkNextSearch.Step) : Word ⊕ Input :=
  cond out.1
    (Sum.inr (p.1, ((betaCode p.2.1.1 p.2.1.2, out.2), p.2.2 ++ [p.2.1])))
    (Sum.inl (p.2.2 ++ [p.2.1, (betaCode p.2.1.1 p.2.1.2, out.2)]))

theorem advance_primrec : Primrec₂ advance := by
  have hp : Primrec (fun p : Input × SkNextSearch.Step => p.1) := Primrec.fst
  have hcontext := Primrec.fst.comp (Primrec.snd.comp hp)
  have hprefix := Primrec.snd.comp (Primrec.snd.comp hp)
  have hbeta := Primrec.comp betaCode_primrec hcontext
  have hnext := hbeta.pair (Primrec.snd.comp Primrec.snd)
  have hsingle := Primrec.list_cons.comp hcontext (Primrec.const [])
  have hpair := Primrec.list_cons.comp hcontext
    (Primrec.list_cons.comp hnext (Primrec.const []))
  have hi := Primrec.sumInr.comp ((Primrec.fst.comp hp).pair
    (hnext.pair (Primrec.list_append.comp hprefix hsingle)))
  have hs := Primrec.sumInl.comp (Primrec.list_append.comp hprefix hpair)
  exact ((Primrec.fst.comp Primrec.snd).cond hi hs).to₂

def dispatch (p : Input) : Part (Word ⊕ Input) :=
  cond (eligible p.1 p.2.1.1 p.2.1.2)
    ((SkNextSearch.execute (p.2.1, p.1)).map (advance p))
    (Part.some (Sum.inl (p.2.2 ++ [p.2.1])))

theorem dispatch_partrec : Partrec dispatch := by
  have hctx : Primrec (fun p : Input => p.2.1) := Primrec.fst.comp Primrec.snd
  have hcut : Primrec (fun p : Input => p.1) := Primrec.fst
  have hcheck := eligible_primrec.comp (hcut.pair hctx)
  have he := SkNextSearch.execute_partrec.comp (hctx.pair hcut).to_comp
  have hmap := Partrec.map he advance_primrec.to_comp
  have hstop := Primrec.sumInl.comp (Primrec.list_append.comp
    (Primrec.snd.comp Primrec.snd) (Primrec.list_cons.comp hctx (Primrec.const [])))
  exact Partrec.cond hcheck.to_comp hmap hstop.to_comp.partrec

theorem dispatch_stop (p : Input) (word : Word)
    (hw : Sum.inl word ∈ dispatch p) :
    (eligible p.1 p.2.1.1 p.2.1.2 = false ∧ word = p.2.2 ++ [p.2.1]) ∨
      (eligible p.1 p.2.1.1 p.2.1.2 = true ∧ ∃ out,
        out ∈ SkNextSearch.execute (p.2.1, p.1) ∧ out.1 = false ∧
          word = p.2.2 ++ [p.2.1, (betaCode p.2.1.1 p.2.1.2, out.2)]) := by
  cases he : eligible p.1 p.2.1.1 p.2.1.2 with
  | false =>
    have hx : word = p.2.2 ++ [p.2.1] := by
      simpa only [dispatch, he, Bool.cond_false, Part.mem_some_iff, Sum.inl.injEq] using hw
    exact Or.inl ⟨he, hx⟩
  | true =>
    rw [dispatch, he, Bool.cond_true] at hw
    obtain ⟨out, ho, hx⟩ := (Part.mem_map_iff (advance p)).mp hw
    cases hh : out.1 with
    | true => simp only [advance, hh, Bool.cond_true, Sum.inr_ne_inl] at hx
    | false =>
      have hword : word = p.2.2 ++ [p.2.1, (betaCode p.2.1.1 p.2.1.2, out.2)] := by
        simpa only [advance, hh, Bool.cond_false, Sum.inl.injEq] using hx.symm
      exact Or.inr ⟨he, out, ho, hh, hword⟩

theorem dispatch_continue (p next : Input)
    (hn : Sum.inr next ∈ dispatch p) :
    eligible p.1 p.2.1.1 p.2.1.2 = true ∧ ∃ out,
      out ∈ SkNextSearch.execute (p.2.1, p.1) ∧ out.1 = true ∧
        next = (p.1, ((betaCode p.2.1.1 p.2.1.2, out.2), p.2.2 ++ [p.2.1])) := by
  cases he : eligible p.1 p.2.1.1 p.2.1.2 with
  | false => simp only [dispatch, he, Bool.cond_false, Part.mem_some_iff, Sum.inr_ne_inl] at hn
  | true =>
    rw [dispatch, he, Bool.cond_true] at hn
    obtain ⟨out, ho, hx⟩ := (Part.mem_map_iff (advance p)).mp hn
    cases hh : out.1 with
    | false => simp only [advance, hh, Bool.cond_false, Sum.inl_ne_inr] at hx
    | true =>
      have hnext : next = (p.1, ((betaCode p.2.1.1 p.2.1.2, out.2), p.2.2 ++ [p.2.1])) := by
        simpa only [advance, hh, Bool.cond_true, Sum.inr.injEq] using hx.symm
      exact ⟨he, out, ho, hh, hnext⟩

theorem dispatch_continue_guard (p next : Input)
    (hn : Sum.inr next ∈ dispatch p) :
    next.1 = p.1 ∧ Mu.inputCheck next.2.1.1 next.2.1.2 = true ∧
      heightCode next.2.1.2 < heightCode p.2.1.2 := by
  obtain ⟨_, out, ho, hh, rfl⟩ := dispatch_continue p next hn
  have hs := SkNextSearch.execute_continue _ _ _ out ho hh
  exact ⟨rfl, hs⟩

theorem dispatch_returns (p : Input) : ∃ result, result ∈ dispatch p := by
  cases he : eligible p.1 p.2.1.1 p.2.1.2 with
  | false =>
    refine ⟨Sum.inl (p.2.2 ++ [p.2.1]), ?_⟩
    simp only [dispatch, he, Bool.cond_false, Part.mem_some_iff]
  | true =>
    have hi := (eligible_exact _ _ _).mp he
    obtain ⟨out, ho⟩ := SkNextSearch.execute_returns _ _ _
      ((SkNextSearch.inputCheck_exact _ _ _).mpr ⟨hi.1, hi.2.1⟩)
    refine ⟨advance p out, ?_⟩
    rw [dispatch, he, Bool.cond_true]
    exact Part.mem_map (advance p) ho

def loop : Input → Part Word := PFun.fix dispatch

theorem loop_partrec : Partrec loop := Partrec.fix dispatch_partrec

/-- Actual recursive branches decrease written height. Strong induction
proves totality of this real partial while loop, without a supplied fuel. -/
theorem loop_returns (p : Input) : ∃ word, word ∈ loop p := by
  have h : ∀ n, ∀ p : Input, heightCode p.2.1.2 = n → ∃ word, word ∈ loop p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp
      obtain ⟨result, hr⟩ := dispatch_returns p
      cases result with
      | inl word => exact ⟨word, PFun.mem_fix_iff.mpr (Or.inl hr)⟩
      | inr next =>
        have hs := dispatch_continue_guard p next hr
        obtain ⟨word, hw⟩ := ih (heightCode next.2.1.2) (by simpa only [hp] using hs.2.2) next rfl
        exact ⟨word, PFun.mem_fix_iff.mpr (Or.inr ⟨next, hr, hw⟩)⟩
  exact h (heightCode p.2.1.2) p rfl

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkIteration.Support
