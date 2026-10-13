import Alexander313.Wilken.PublicEpsilonNativeSkSourcePathSupport
import Mathlib.Data.List.Forall2

/-!
# Actual chronological finite-code search at one original sk source

The real partial loop searches each canonical public entry at the literal
original q and appends the resulting Normal LOW code chronologically. A
derived caller for every entry proves termination by list induction.
Real fix induction identifies its output with the original ordinal-value
word. No representative, search bound, endpoint, Par or spelling oracle
is supplied. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkSourceWord.Support

abbrev Word := SkIteration.Support.Word
abbrev State := Nat × (Word × List Nat)

def EntryMatches (q : Nat) (entry : Context) (d : Nat) : Prop :=
  lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true ∧
    interpretation q d = interpretation entry.1 entry.2

def step (p : State) : Part (List Nat ⊕ State) := cond (p.2.1.length == 0)
  (Part.some (Sum.inl p.2.2))
  ((SkNextSearch.Support.search p.1 (UniformPublicReturn.publicCode
    ((p.2.1.head?).getD (0, 0)).1 ((p.2.1.head?).getD (0, 0)).2)).map fun d =>
      Sum.inr (p.1, (p.2.1.tail, p.2.2 ++ [d])))

theorem step_partrec : Partrec step := by
  have hq : Primrec (fun p : State => p.1) := Primrec.fst
  have hw : Primrec (fun p : State => p.2.1) := Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun p : State => p.2.2) := Primrec.snd.comp Primrec.snd
  have hz := Primrec.beq.comp (Primrec.list_length.comp hw) (Primrec.const 0)
  have hh := Primrec.option_getD.comp (Primrec.list_head?.comp hw) (Primrec.const (0, 0))
  have hu := UniformPublicReturn.publicCode_primrec.comp (Primrec.fst.comp hh) (Primrec.snd.comp hh)
  have hs := SkNextSearch.Support.search_partrec.comp hq.to_comp hu.to_comp
  have hm : Computable₂ (fun p : State => fun d : Nat =>
      Sum.inr (p.1, (p.2.1.tail, p.2.2 ++ [d])) : List Nat ⊕ State) :=
    (Primrec.sumInr.comp ((hq.comp Primrec.fst).pair
      ((Primrec.list_tail.comp (hw.comp Primrec.fst)).pair
        (Primrec.list_append.comp (hp.comp Primrec.fst)
          (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))))).to_comp.to₂
  exact Partrec.cond hz.to_comp (Primrec.sumInl.comp hp).to_comp.partrec (Partrec.map hs hm)

theorem step_nil (q : Nat) (prefix : List Nat) :
    step (q, ([], prefix)) = Part.some (Sum.inl prefix) := by simp only [step, List.length_nil, beq_self_eq_true, Bool.cond_true]

theorem step_cons (q : Nat) (entry : Context) (rest : Word) (prefix : List Nat) :
    step (q, (entry :: rest, prefix)) =
      (SkNextSearch.Support.search q (UniformPublicReturn.publicCode entry.1 entry.2)).map
        (fun d => Sum.inr (q, (rest, prefix ++ [d]))) := by
  simp [step]

theorem step_stop (p : State) (out : List Nat) (ho : Sum.inl out ∈ step p) :
    p.2.1 = [] ∧ out = p.2.2 := by
  rcases p with ⟨q, word, prefix⟩
  cases word with
  | nil =>
    rw [step_nil] at ho
    exact ⟨rfl, by simpa only [Part.mem_some_iff, Sum.inl.injEq] using ho⟩
  | cons entry rest =>
    rw [step_cons] at ho
    obtain ⟨d, hd, he⟩ := (Part.mem_map_iff _).mp ho
    simp only [Sum.inr_ne_inl] at he

theorem step_continue (p next : State) (hn : Sum.inr next ∈ step p) :
    ∃ entry rest d, p.2.1 = entry :: rest ∧
      d ∈ SkNextSearch.Support.search p.1 (UniformPublicReturn.publicCode entry.1 entry.2) ∧
        next = (p.1, (rest, p.2.2 ++ [d])) := by
  rcases p with ⟨q, word, prefix⟩
  cases word with
  | nil =>
    rw [step_nil] at hn
    simp only [Part.mem_some_iff, Sum.inr_ne_inl] at hn
  | cons entry rest =>
    rw [step_cons] at hn
    obtain ⟨d, hd, he⟩ := (Part.mem_map_iff _).mp hn
    exact ⟨entry, rest, d, rfl, hd, Sum.inr.inj he.symm⟩

def loop : State → Part (List Nat) := PFun.fix step

theorem loop_partrec : Partrec loop := Partrec.fix step_partrec

/-- Termination follows from the actual finite remaining word and a real
derived search return for each entry; no numerical search bound is used. -/
theorem loop_returns (q : Nat) (word : Word) (prefix : List Nat)
    (hs : ∀ entry ∈ word, ∃ d, d ∈ SkNextSearch.Support.search q
      (UniformPublicReturn.publicCode entry.1 entry.2)) :
    ∃ out, out ∈ loop (q, (word, prefix)) := by
  revert prefix hs
  induction word with
  | nil =>
    intro prefix hs
    exact ⟨prefix, PFun.mem_fix_iff.mpr (Or.inl (by rw [step_nil]; exact Part.mem_some _))⟩
  | cons entry rest ih =>
    intro prefix hs
    obtain ⟨d, hd⟩ := hs entry List.mem_cons_self
    obtain ⟨out, ho⟩ := ih (prefix ++ [d])
      (fun e he => hs e (List.mem_cons_of_mem _ he))
    exact ⟨out, PFun.mem_fix_iff.mpr (Or.inr ⟨(q, (rest, prefix ++ [d])),
      by rw [step_cons]; exact Part.mem_map _ hd, ho⟩)⟩

/-- Genuine search membership and actual public-return values identify
the entire chronological output with checked original-q LOW syntax. -/
theorem loop_relation (p : State) (out : List Nat) (ho : out ∈ loop p)
    (hl : ∀ entry ∈ p.2.1, lowCheckCode entry.1 entry.2 = true) :
    ∃ tail, out = p.2.2 ++ tail ∧ List.Forall₂ (EntryMatches p.1) p.2.1 tail := by
  let C : State → Prop := fun s =>
    (∀ entry ∈ s.2.1, lowCheckCode entry.1 entry.2 = true) →
      ∃ tail, out = s.2.2 ++ tail ∧ List.Forall₂ (EntryMatches s.1) s.2.1 tail
  have h : C p := by
    apply PFun.fixInduction (C := C) ho
    intro s hs ih hlow
    rcases PFun.mem_fix_iff.mp hs with hstop | ⟨next, hn, hout⟩
    · obtain ⟨hnil, he⟩ := step_stop s out hstop
      exact ⟨[], by simpa only [List.append_nil] using he, by rw [hnil]; exact .nil⟩
    · obtain ⟨entry, rest, d, hword, hd, hnext⟩ := step_continue s next hn
      have hrest : ∀ e ∈ rest, lowCheckCode e.1 e.2 = true := by
        intro e he
        exact hlow e (by rw [hword]; exact List.mem_cons_of_mem _ he)
      obtain ⟨tail, he, hrel⟩ := ih next hn (by rw [hnext]; exact hrest)
      rw [hnext] at he hrel
      have hc := SkNextSearch.Support.search_spec s.1 _ d hd
      have hp := UniformPublicReturn.publicCode_spec entry.1 entry.2
        ((UniformPublicReturn.inputCheck_exact _ _).mpr
          (hlow entry (by rw [hword]; exact List.mem_cons_self)))
      refine ⟨d :: tail, ?_, ?_⟩
      · simpa only [List.append_assoc, List.singleton_append] using he
      · rw [hword]
        exact .cons ⟨hc.1, hc.2.1, hc.2.2.2.trans hp.2⟩ hrel
  exact h hl

theorem relation_values (q : Nat) {word : Word} {codes : List Nat}
    (hr : List.Forall₂ (EntryMatches q) word codes) :
    codes.map (interpretation q) = word.map (fun entry => interpretation entry.1 entry.2) := by
  induction hr with
  | nil => rfl
  | cons he ht ih => simp only [List.map_cons, he.2.2, ih]

theorem relation_checked (q : Nat) {word : Word} {codes : List Nat}
    (hr : List.Forall₂ (EntryMatches q) word codes) :
    ∀ d ∈ codes, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true := by
  induction hr with
  | nil => intro d hd; exact False.elim (List.not_mem_nil hd)
  | cons he ht ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨he.1, he.2.1⟩
    · exact ih d hd

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkSourceWord.Support
