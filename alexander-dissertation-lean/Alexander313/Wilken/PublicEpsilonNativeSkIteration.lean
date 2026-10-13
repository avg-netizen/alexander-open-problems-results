import Alexander313.Wilken.PublicEpsilonNativeSkIterationSupport

/-!
# Executing finite native sk recurrence with original guards

The actual partial while loop retains chronological source-context/code
pairs. It stops when the original cutoff exceeds current mu, or when the
actual truncated next value fails the epsilon-above-current test. Every
recursive continuation is a genuine HIGH root with strictly smaller
written height, so the real loop terminates. Its output has the literal
finite recurrence certificate below. This establishes the native recurrence
and maximal stopping condition; original source-one initialization, a flat
single-context tracking spelling, Par transport and evaluation are separate.
No fuel, halt, plus, representative or recurrence oracle is assumed.
All source candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkIteration

open Support

/-- A finite certificate retains the actual next execution, both genuine
stopping alternatives, and precisely the true continuation branches. -/
inductive Path (cutoff : Nat) : Context → Word → Prop
  | stop (q root : Nat) (ha : Mu.inputCheck q root = true)
      (hc : unionCheck cutoff = true) (hb : Mu.sourceValue q root < unionInterpretation cutoff) :
      Path cutoff (q, root) [(q, root)]
  | nextStop (q root : Nat) (out : SkNextSearch.Step)
      (he : eligible cutoff q root = true)
      (ho : out ∈ SkNextSearch.execute ((q, root), cutoff)) (hh : out.1 = false) :
      Path cutoff (q, root) [(q, root), (betaCode q root, out.2)]
  | nextContinue (q root : Nat) (out : SkNextSearch.Step) (tail : Word)
      (he : eligible cutoff q root = true)
      (ho : out ∈ SkNextSearch.execute ((q, root), cutoff)) (hh : out.1 = true)
      (ht : Path cutoff (betaCode q root, out.2) tail) :
      Path cutoff (q, root) ((q, root) :: tail)

theorem Path.head {cutoff : Nat} {ctx : Context} {word : Word} (hp : Path cutoff ctx word) :
    ∃ tail, word = ctx :: tail := by
  cases hp with
  | stop => exact ⟨[], rfl⟩
  | nextStop q root out => exact ⟨[(betaCode q root, out.2)], rfl⟩
  | nextContinue q root out tail => exact ⟨tail, rfl⟩

theorem Path.nonempty {cutoff : Nat} {ctx : Context} {word : Word} (hp : Path cutoff ctx word) :
    word ≠ [] := by
  obtain ⟨tail, rfl⟩ := hp.head
  exact List.cons_ne_nil _ _

theorem Path.checked {cutoff : Nat} {ctx : Context} {word : Word} (hp : Path cutoff ctx word) :
    ∀ entry ∈ word, lowCheckCode entry.1 entry.2 = true ∧
      Comparison.acceptedCode entry.1 entry.2 = true := by
  induction hp with
  | stop q root ha hc hb =>
    intro entry hm
    rw [List.mem_singleton.mp hm]
    exact ⟨RootLowCollapse.root_low q root ha, RootLowCollapse.root_accepted q root ha⟩
  | nextStop q root out he ho hh =>
    intro entry hm
    have ha := ((eligible_exact cutoff q root).mp he).1
    have hs := SkNextSearch.execute_spec q root cutoff out ho
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨RootLowCollapse.root_low q root ha, RootLowCollapse.root_accepted q root ha⟩
    · rw [List.mem_singleton.mp hm]
      exact ⟨hs.2.1, hs.2.2.1⟩
  | nextContinue q root out tail he ho hh ht ih =>
    intro entry hm
    rcases List.mem_cons.mp hm with rfl | hm
    · have ha := ((eligible_exact cutoff q root).mp he).1
      exact ⟨RootLowCollapse.root_low q root ha, RootLowCollapse.root_accepted q root ha⟩
    · exact ih entry hm

/-- Every proper recurrence edge is exactly the actual overlined truncation
of current mu, with its original eligibility comparison already proved. -/
theorem Path.first_step {cutoff : Nat} {q root : Nat} {next : Context} {tail : Word}
    (hp : Path cutoff (q, root) ((q, root) :: next :: tail)) :
    ∃ out, out ∈ SkNextSearch.execute ((q, root), cutoff) ∧
      next = (betaCode q root, out.2) ∧
      unionInterpretation cutoff ≤ Mu.sourceValue q root ∧
      interpretation next.1 next.2 = SkNextStep.nextValue q root (unionInterpretation cutoff) := by
  cases hp with
  | nextStop q root out he ho hh =>
    exact ⟨out, ho, rfl, ((eligible_exact cutoff q root).mp he).2.2,
      (SkNextSearch.execute_spec q root cutoff out ho).2.2.2.1⟩
  | nextContinue q root out tail he ho hh ht =>
    obtain ⟨rest, hhead⟩ := ht.head
    have hn := (List.cons.inj hhead).1
    exact ⟨out, ho, hn, ((eligible_exact cutoff q root).mp he).2.2,
      by rw [hn]; exact (SkNextSearch.execute_spec q root cutoff out ho).2.2.2.1⟩

def Terminal (cutoff : Nat) (entry : Context) : Prop :=
  (Mu.inputCheck entry.1 entry.2 = true ∧
    Mu.sourceValue entry.1 entry.2 < unionInterpretation cutoff) ∨
      ∃ q root out, eligible cutoff q root = true ∧
        out ∈ SkNextSearch.execute ((q, root), cutoff) ∧ out.1 = false ∧
          entry = (betaCode q root, out.2)

/-- The final position is an actual maximal stopping alternative: either
the current epsilon's mu is below the cutoff, or the emitted next value
fails the true epsilon-above-current continuation test. -/
theorem Path.terminal {cutoff : Nat} {ctx : Context} {word : Word} (hp : Path cutoff ctx word) :
    ∃ before final, word = before ++ [final] ∧ Terminal cutoff final := by
  induction hp with
  | stop q root ha hc hb => exact ⟨[], (q, root), rfl, Or.inl ⟨ha, hb⟩⟩
  | nextStop q root out he ho hh =>
    exact ⟨[(q, root)], (betaCode q root, out.2), rfl, Or.inr ⟨q, root, out, he, ho, hh, rfl⟩⟩
  | nextContinue q root out tail he ho hh ht ih =>
    obtain ⟨before, final, hword, hfinal⟩ := ih
    exact ⟨(q, root) :: before, final, by rw [hword]; rfl, hfinal⟩

/-- The genuine source M>1 class gives the printed lower bound for every
position after the initial root, including an emitted stopping value. -/
theorem Path.tail_bounds {cutoff : Nat} {ctx : Context} {word : Word} (hp : Path cutoff ctx word)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hpos : 1 < unionInterpretation cutoff) :
    ∀ entry ∈ word.tail, unionInterpretation cutoff ≤ interpretation entry.1 entry.2 := by
  induction hp with
  | stop q root ha hc hb => intro entry he; exact False.elim (List.not_mem_nil he)
  | nextStop q root out he ho hh =>
    intro entry hen
    have hentry : entry = (betaCode q root, out.2) := by
      simpa only [List.tail_cons, List.mem_singleton] using hen
    rw [hentry]
    exact (SkNextSearch.execute_source_bounds q root cutoff out ho hm hpos
      ((eligible_exact cutoff q root).mp he).2.2).1
  | nextContinue q root out tail he ho hh ht ih =>
    intro entry hen
    obtain ⟨rest, hr⟩ := ht.head
    have hmem : entry ∈ (betaCode q root, out.2) :: rest := by
      simpa only [List.tail_cons, hr] using hen
    rcases List.mem_cons.mp hmem with rfl | heRest
    · exact (SkNextSearch.execute_source_bounds q root cutoff out ho hm hpos
        ((eligible_exact cutoff q root).mp he).2.2).1
    · apply ih entry
      simpa only [hr, List.tail_cons] using heRest

theorem loop_path (p : Input) (word : Word) (hw : word ∈ loop p)
    (ha : Mu.inputCheck p.2.1.1 p.2.1.2 = true) (hc : unionCheck p.1 = true) :
    ∃ tail, word = p.2.2 ++ tail ∧ Path p.1 p.2.1 tail := by
  let C : Input → Prop := fun s => Mu.inputCheck s.2.1.1 s.2.1.2 = true →
    unionCheck s.1 = true → ∃ tail, word = s.2.2 ++ tail ∧ Path s.1 s.2.1 tail
  have h : C p := by
    apply PFun.fixInduction (C := C) hw
    intro s hs ih hroot hcut
    rcases PFun.mem_fix_iff.mp hs with hstop | ⟨next, hn, hnext⟩
    · rcases dispatch_stop s word hstop with ⟨he, hword⟩ | ⟨he, out, ho, hh, hword⟩
      · exact ⟨[s.2.1], hword, .stop _ _ hroot hcut
          ((ineligible_exact _ _ _ hroot hcut).mp he)⟩
      · exact ⟨[s.2.1, (betaCode s.2.1.1 s.2.1.2, out.2)], hword,
          .nextStop _ _ out he ho hh⟩
    · obtain ⟨he, out, ho, hh, hstate⟩ := dispatch_continue s next hn
      have hguard := dispatch_continue_guard s next hn
      obtain ⟨tail, hword, hpath⟩ := ih next hn hguard.2.1 (by rw [hguard.1]; exact hcut)
      rw [hstate] at hword hpath
      refine ⟨s.2.1 :: tail, ?_, .nextContinue _ _ out tail he ho hh hpath⟩
      simpa only [List.append_assoc, List.singleton_append] using hword
  exact h ha hc

def inputCheck (q root cutoff : Nat) : Bool := SkNextSearch.inputCheck q root cutoff

theorem inputCheck_primrec : Primrec (fun p : SkNextSearch.Support.Query =>
    inputCheck p.1.1 p.1.2 p.2) := SkNextSearch.inputCheck_primrec

theorem inputCheck_exact (q root cutoff : Nat) : inputCheck q root cutoff = true ↔
    Mu.inputCheck q root = true ∧ unionCheck cutoff = true := SkNextSearch.inputCheck_exact _ _ _

def execute (p : SkNextSearch.Support.Query) : Part Word := cond (inputCheck p.1.1 p.1.2 p.2)
  (loop (p.2, (p.1, []))) Part.none

theorem execute_partrec : Partrec execute :=
  Partrec.cond inputCheck_primrec.to_comp
    (loop_partrec.comp (Primrec.snd.pair (Primrec.fst.pair (Primrec.const []))).to_comp) Partrec.none

theorem execute_domain (q root cutoff : Nat) : (execute ((q, root), cutoff)).Dom ↔
    inputCheck q root cutoff = true := by
  constructor
  · intro hd
    cases hi : inputCheck q root cutoff with
    | true => rfl
    | false =>
      have hx : (Part.none : Part Word).Dom := by simpa only [execute, hi, Bool.cond_false] using hd
      exact False.elim (Part.not_none_dom hx)
  · intro hi
    obtain ⟨word, hw⟩ := loop_returns (cutoff, ((q, root), []))
    apply Part.dom_iff_mem.mpr
    exact ⟨word, by simpa only [execute, hi, Bool.cond_true] using hw⟩

theorem execute_returns (q root cutoff : Nat) (hi : inputCheck q root cutoff = true) :
    ∃ word, word ∈ execute ((q, root), cutoff) :=
  Part.dom_iff_mem.mp ((execute_domain q root cutoff).mpr hi)

theorem execute_spec (q root cutoff : Nat) (word : Word)
    (hw : word ∈ execute ((q, root), cutoff)) :
    inputCheck q root cutoff = true ∧ Path cutoff (q, root) word ∧
      word ≠ [] ∧ ∀ entry ∈ word, lowCheckCode entry.1 entry.2 = true ∧
        Comparison.acceptedCode entry.1 entry.2 = true := by
  have hi := (execute_domain q root cutoff).mp (Part.dom_iff_mem.mpr ⟨word, hw⟩)
  have hs := (inputCheck_exact q root cutoff).mp hi
  rw [execute, hi, Bool.cond_true] at hw
  obtain ⟨tail, hword, hp⟩ := loop_path (cutoff, ((q, root), [])) word hw hs.1 hs.2
  have he : word = tail := by simpa only [List.nil_append] using hword
  subst tail
  exact ⟨hi, hp, hp.nonempty, hp.checked⟩

theorem execute_initial (q root cutoff : Nat) (word : Word)
    (hw : word ∈ execute ((q, root), cutoff)) : ∃ tail, word = (q, root) :: tail :=
  ((execute_spec q root cutoff word hw).2.1).head

theorem execute_terminal (q root cutoff : Nat) (word : Word)
    (hw : word ∈ execute ((q, root), cutoff)) :
    ∃ before final, word = before ++ [final] ∧ Terminal cutoff final :=
  ((execute_spec q root cutoff word hw).2.1).terminal

theorem execute_source_bounds (q root cutoff : Nat) (word : Word)
    (hw : word ∈ execute ((q, root), cutoff))
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation cutoff))
    (hpos : 1 < unionInterpretation cutoff) :
    ∀ entry ∈ word.tail, unionInterpretation cutoff ≤ interpretation entry.1 entry.2 :=
  ((execute_spec q root cutoff word hw).2.1).tail_bounds hm hpos

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkIteration
