import Alexander313.Wilken.PublicEpsilonNativeLocalizationSupport

/-!
# Genuine same-base localization at every original coded epsilon

The real native-q comparator folds the full written zero support by
greatest ARGUMENT among values above the current value. The actual finite
live-list walk derives every SourcePath clause and ends at the original
root value. True exposed witnesses and strictly smaller written syntax
derive the argument-gap property of every actual selection. No public
return, base-changing localization, endpoint or gap oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization

open ThetaCourse

def choose (q c : Nat) (tail : Option Nat) : Option Nat :=
  match tail with
  | none => some c
  | some d => some (cond (Normalization.lessRawCode q (argumentCode d) (argumentCode c)) c d)

theorem choose_primrec : Primrec (fun p : Nat × (Nat × Option Nat) => choose p.1 p.2.1 p.2.2) := by
  have ho := Primrec.snd.comp Primrec.snd
  have hc := Primrec.fst.comp Primrec.snd
  have hr := Primrec.fst.comp Primrec.fst
  have hcan := hc.comp Primrec.fst
  have ht := Normalization.Effective.lessRawCode_primrec.comp
    (hr.pair ((argumentCode_primrec.comp Primrec.snd).pair (argumentCode_primrec.comp hcan)))
  exact Primrec.option_casesOn ho (Primrec.option_some.comp hc)
    (Primrec.option_some.comp (Primrec.cond ht hcan Primrec.snd)).to₂

def best (q : Nat) : List Nat → Option Nat
  | [] => none
  | c :: cs => choose q c (best q cs)

theorem best_primrec : Primrec₂ best := by
  have hs : Primrec₂ (fun (p : Nat × List Nat) (s : Nat × Option Nat) => choose p.1 s.1 s.2) :=
    (choose_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const none) hs
  have he : (fun p : Nat × List Nat => p.2.foldr (fun c o => choose p.1 c o) none) =
      fun p => best p.1 p.2 := by
    funext p
    induction p.2 with
    | nil => rfl
    | cons c cs ih => simp only [List.foldr_cons, best, ih]
  rw [he] at h
  exact h.to₂

theorem best_none (q : Nat) (xs : List Nat) : best q xs = none ↔ xs = [] := by
  cases xs with
  | nil => simp only [best]
  | cons c cs => cases best q cs <;> simp only [best, choose, Option.some_ne_none, List.cons_ne_nil]

theorem best_mem (q : Nat) (xs : List Nat) (c : Nat) (hc : best q xs = some c) : c ∈ xs := by
  induction xs with
  | nil => simp only [best, Option.none_ne_some] at hc
  | cons a xs ih =>
    cases ht : best q xs with
    | none => have he : a = c := by simpa only [best, ht, choose, Option.some.injEq] using hc
              rw [← he]; exact List.mem_cons_self
    | some d =>
      cases hl : Normalization.lessRawCode q (argumentCode d) (argumentCode a) with
      | false =>
        have he : d = c := by simpa only [best, ht, choose, hl, Bool.cond_false, Option.some.injEq] using hc
        rw [← he]; exact List.mem_cons_of_mem _ (ih ht)
      | true =>
        have he : a = c := by simpa only [best, ht, choose, hl, Bool.cond_true, Option.some.injEq] using hc
        rw [← he]; exact List.mem_cons_self

theorem best_maximal (q : Nat) (xs : List Nat) (hx : ∀ c ∈ xs, Node q c)
    (c : Nat) (hc : best q xs = some c) : ∀ d ∈ xs, argumentValue q d ≤ argumentValue q c := by
  revert hx c hc
  induction xs with
  | nil => intro _ c hc; simp only [best, Option.none_ne_some] at hc
  | cons a xs ih =>
    intro hx c hc
    have ha := hx a List.mem_cons_self
    have htail := fun d hd => hx d (List.mem_cons_of_mem _ hd)
    cases ht : best q xs with
    | none =>
      have hxnil := (best_none q xs).mp ht
      subst xs
      have he : a = c := by simpa only [best, choose, Option.some.injEq] using hc
      subst c
      intro d hd
      have he := List.mem_singleton.mp hd
      rw [he]
    | some b =>
      have hb := htail b (best_mem q xs b ht)
      have hm := ih htail b ht
      cases hl : Normalization.lessRawCode q (argumentCode b) (argumentCode a) with
      | false =>
        have he : b = c := by simpa only [best, ht, choose, hl, Bool.cond_false, Option.some.injEq] using hc
        subst c
        have hab : argumentValue q a ≤ argumentValue q b := le_of_not_gt (fun h => by
          have hh := (argument_less_exact q b a hb ha).mpr h
          simp only [hl, Bool.false_eq_true] at hh)
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hab
        · exact hm d hd
      | true =>
        have he : a = c := by simpa only [best, ht, choose, hl, Bool.cond_true, Option.some.injEq] using hc
        subst c
        have hba := (argument_less_exact q b a hb ha).mp hl
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact le_rfl
        · exact (hm d hd).trans hba.le

/-- Remove every node whose value is at most the new current value. -/
def live (q current : Nat) : List Nat → List Nat
  | [] => []
  | c :: cs => cond (Normalization.lessRawCode q current c) (c :: live q current cs) (live q current cs)

theorem live_primrec : Primrec (fun p : Nat × (Nat × List Nat) => live p.1 p.2.1 p.2.2) := by
  have hr := Primrec.fst.comp Primrec.fst
  have hcur := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hc := Primrec.fst.comp Primrec.snd
  have htail := Primrec.snd.comp Primrec.snd
  have ht := Normalization.Effective.lessRawCode_primrec.comp (hr.pair (hcur.pair hc))
  have hs : Primrec₂ (fun (p : Nat × (Nat × List Nat)) (s : Nat × List Nat) =>
      cond (Normalization.lessRawCode p.1 p.2.1 s.1) (s.1 :: s.2) s.2) := by
    exact (Primrec.cond ht (Primrec.list_cons.comp hc htail) htail).to₂
  have h := Primrec.list_foldr (Primrec.snd.comp Primrec.snd) (Primrec.const []) hs
  have he : (fun p : Nat × (Nat × List Nat) => p.2.2.foldr
      (fun c xs => cond (Normalization.lessRawCode p.1 p.2.1 c) (c :: xs) xs) []) =
        fun p => live p.1 p.2.1 p.2.2 := by
    funext p
    induction p.2.2 with
    | nil => rfl
    | cons c cs ih => simp only [List.foldr_cons, live, ih]
  rw [he] at h
  exact h

theorem live_mem (q current : Nat) (xs : List Nat) (c : Nat) :
    c ∈ live q current xs ↔ c ∈ xs ∧ Normalization.lessRawCode q current c = true := by
  induction xs with
  | nil => simp only [live, List.not_mem_nil, false_and]
  | cons a xs ih =>
    cases ht : Normalization.lessRawCode q current a with
    | false =>
      simp only [live, ht, Bool.cond_false, ih, List.mem_cons]
      constructor
      · intro h; exact ⟨Or.inr h.1, h.2⟩
      · rintro ⟨h | h, hc⟩
        · subst c; simp only [ht, Bool.false_eq_true] at hc
        · exact ⟨h, hc⟩
    | true =>
      simp only [live, ht, Bool.cond_true, List.mem_cons, ih]
      constructor
      · rintro (h | h)
        · subst c; exact ⟨Or.inl rfl, ht⟩
        · exact ⟨Or.inr h.1, h.2⟩
      · rintro ⟨h | h, hc⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, hc⟩

theorem live_length_le (q current : Nat) (xs : List Nat) : (live q current xs).length ≤ xs.length := by
  induction xs with
  | nil => exact le_rfl
  | cons a xs ih => cases ht : Normalization.lessRawCode q current a <;> simp only [live, ht,
      Bool.cond_false, Bool.cond_true, List.length_cons] <;> omega

theorem live_length_lt (q current : Nat) (xs : List Nat) (c : Nat) (hc : c ∈ xs)
    (hfalse : Normalization.lessRawCode q current c = false) : (live q current xs).length < xs.length := by
  revert hc
  induction xs with
  | nil => intro hc; exact False.elim (List.not_mem_nil hc)
  | cons a xs ih =>
    intro hc
    rcases List.mem_cons.mp hc with he | hc
    · subst a
      simpa only [live, hfalse, Bool.cond_false, List.length_cons] using
        Nat.lt_succ_of_le (live_length_le q current xs)
    · have ht := ih hc
      cases hl : Normalization.lessRawCode q current a <;> simp only [live, hl,
        Bool.cond_false, Bool.cond_true, List.length_cons] <;> omega

abbrev State := (Nat × List Nat) × List Nat

/-- The last component records earlier values in chronological order. -/
def step (q : Nat) (s : State) : State :=
  match best q s.1.2 with
  | none => s
  | some c => ((c, live q c s.1.2), s.2 ++ [s.1.1])

theorem step_primrec : Primrec₂ step := by
  have hr := Primrec.fst.comp Primrec.fst
  have hs := Primrec.snd.comp Primrec.fst
  have hxs := Primrec.snd.comp (Primrec.fst.comp hs)
  have hcur := Primrec.fst.comp (Primrec.fst.comp hs)
  have hout := Primrec.snd.comp hs
  have hl := live_primrec.comp (hr.pair (Primrec.snd.pair hxs))
  have hb := best_primrec.comp Primrec.fst (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hnew := (Primrec.snd.pair hl).pair (Primrec.list_concat.comp hout hcur)
  exact (Primrec.option_casesOn hb Primrec.snd hnew.to₂).to₂

def iterate (q : Nat) : Nat → State → State
  | 0, s => s
  | n + 1, s => step q (iterate q n s)

theorem iterate_primrec : Primrec₂ (fun p : Nat × State => fun n : Nat => iterate p.1 n p.2) :=
  Primrec.nat_rec Primrec.snd
    ((step_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)).to₂)

theorem iterate_succ_start (q n : Nat) (s : State) : iterate q (n + 1) s = iterate q n (step q s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterate, ih]

def addPrefix (p : List Nat) (s : State) : State := (s.1, p ++ s.2)

theorem step_addPrefix (q : Nat) (p : List Nat) (s : State) : step q (addPrefix p s) = addPrefix p (step q s) := by
  cases hb : best q s.1.2 <;> simp only [step, addPrefix, hb, List.append_assoc]

theorem iterate_addPrefix (q n : Nat) (p : List Nat) (s : State) :
    iterate q n (addPrefix p s) = addPrefix p (iterate q n s) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate, ih, step_addPrefix]; rfl

def finish (s : State) : List Nat := s.2 ++ [s.1.1]

def walk (fuel q current : Nat) (xs : List Nat) : List Nat :=
  finish (iterate q fuel ((current, xs), []))

theorem walk_zero (q current : Nat) (xs : List Nat) : walk 0 q current xs = [current] := rfl

theorem walk_succ (n q current : Nat) (xs : List Nat) : walk (n + 1) q current xs =
    match best q xs with
    | none => [current]
    | some c => current :: walk n q c (live q c xs) := by
  rw [walk, iterate_succ_start]
  cases hb : best q xs with
  | none =>
    have hs : step q ((current, xs), []) = ((current, xs), []) := by simp only [step, hb]
    have hi : iterate q n ((current, xs), []) = ((current, xs), []) := by
      induction n with
      | zero => rfl
      | succ n ih => rw [iterate, ih, hs]
    simp only [step, hb, hi, finish, List.nil_append]
  | some c =>
    have hs : step q ((current, xs), []) = addPrefix [current] ((c, live q c xs), []) := by
      simp only [step, hb, addPrefix, List.nil_append]
    rw [hs, iterate_addPrefix]
    simp only [finish, addPrefix, walk, List.cons_append, List.nil_append, List.append_assoc]

/-- The exact surviving support after the current value has been reached. -/
def Available (q current : Nat) (source xs : List Nat) : Prop :=
  ∀ c, c ∈ xs ↔ c ∈ source ∧ value q current < value q c

/-- Literal source recurrence, greatest argument, and absence of a further step. -/
inductive SourcePath (q : Nat) (source : List Nat) : List Nat → Prop
  | stop (c : Nat) (hc : Node q c) (hmax : ∀ d ∈ source, value q d ≤ value q c) : SourcePath q source [c]
  | next (c d : Nat) (tail : List Nat) (hc : Node q c) (hcd : value q c < value q d)
      (hd : d ∈ source) (harg : ∀ e ∈ source, value q c < value q e → argumentValue q e ≤ argumentValue q d)
      (hrest : SourcePath q source (d :: tail)) : SourcePath q source (c :: d :: tail)

theorem walk_head (fuel q current : Nat) (xs : List Nat) :
    ∃ tail : List Nat, walk fuel q current xs = current :: tail := by
  induction fuel generalizing current xs with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    rw [walk_succ]
    cases best q xs with
    | none => exact ⟨[], rfl⟩
    | some c => exact ⟨walk n q c (live q c xs), rfl⟩

theorem walk_source (fuel q current : Nat) (source xs : List Nat)
    (hcur : Node q current) (hs : ∀ c ∈ source, Node q c)
    (ha : Available q current source xs) (hbudget : xs.length ≤ fuel) :
    SourcePath q source (walk fuel q current xs) := by
  revert current xs
  induction fuel with
  | zero =>
    intro current xs hcur ha hbudget
    have hnil : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hbudget)
    rw [walk_zero]
    apply SourcePath.stop current hcur
    intro d hd
    apply le_of_not_gt
    intro hlt
    have hm := (ha d).mpr ⟨hd, hlt⟩
    rw [hnil] at hm
    exact List.not_mem_nil hm
  | succ n ih =>
    intro current xs hcur ha hbudget
    rw [walk_succ]
    cases hb : best q xs with
    | none =>
      apply SourcePath.stop current hcur
      intro d hd
      apply le_of_not_gt
      intro hlt
      have hm := (ha d).mpr ⟨hd, hlt⟩
      rw [(best_none q xs).mp hb] at hm
      exact List.not_mem_nil hm
    | some c =>
      have hcx := best_mem q xs c hb
      have hcs := (ha c).mp hcx
      have hcn := hs c hcs.1
      have hnodes : ∀ d ∈ xs, Node q d := fun d hd => hs d ((ha d).mp hd).1
      have hself : Normalization.lessRawCode q c c = false := Bool.eq_false_of_not_eq_true
        (fun h => (lt_irrefl (value q c)) ((value_less_exact q c c hcn hcn).mp h))
      have hsmall := live_length_lt q c xs c hcx hself
      have hnext : Available q c source (live q c xs) := by
        intro d
        rw [live_mem]
        constructor
        · rintro ⟨hd, hlt⟩
          exact ⟨((ha d).mp hd).1, (value_less_exact q c d hcn (hnodes d hd)).mp hlt⟩
        · rintro ⟨hd, hlt⟩
          have hdx := (ha d).mpr ⟨hd, hcs.2.trans hlt⟩
          exact ⟨hdx, (value_less_exact q c d hcn (hs d hd)).mpr hlt⟩
      have hbound : (live q c xs).length ≤ n := by omega
      have hpath := ih c (live q c xs) hcn hnext hbound
      obtain ⟨tail, he⟩ := walk_head n q c (live q c xs)
      rw [he] at hpath ⊢
      exact SourcePath.next current c tail hcur hcs.2 hcs.1
        (fun d hd hlt => best_maximal q xs hnodes c hb d ((ha d).mpr ⟨hd, hlt⟩)) hpath

theorem finish_primrec : Primrec finish :=
  Primrec.list_concat.comp Primrec.snd (Primrec.fst.comp Primrec.fst)

theorem walk_primrec : Primrec (fun p : Nat × (Nat × (Nat × List Nat)) =>
    walk p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hr := Primrec.fst.comp Primrec.snd
  have hi := (Primrec.snd.comp Primrec.snd).pair (Primrec.const [])
  exact finish_primrec.comp (iterate_primrec.comp (hr.pair hi) Primrec.fst)

theorem walk_length_le (fuel q current : Nat) (xs : List Nat) : (walk fuel q current xs).length ≤ fuel + 1 := by
  induction fuel generalizing current xs with
  | zero => exact le_rfl
  | succ n ih =>
    rw [walk_succ]
    cases best q xs with
    | none => simp only [List.length_singleton]; omega
    | some c => simpa only [List.length_cons] using Nat.succ_le_succ (ih c (live q c xs))

/-- The endpoint of a literal nonempty sequence, with an auxiliary empty default. -/
def endpoint : List Nat → Nat
  | [] => 0
  | [c] => c
  | _ :: d :: tail => endpoint (d :: tail)

theorem SourcePath.nodes {q : Nat} {source path : List Nat} (hp : SourcePath q source path) :
    ∀ c ∈ path, Node q c := by
  induction hp with
  | stop c hc hmax => intro d hd; rw [List.mem_singleton.mp hd]; exact hc
  | next c d tail hc hcd hd harg hp ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hc
    · exact ih e he

theorem SourcePath.head_le {q : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : SourcePath q source (c :: tail)) : ∀ d ∈ c :: tail, value q c ≤ value q d := by
  induction hp with
  | stop c hc hmax => intro d hd; rw [List.mem_singleton.mp hd]
  | next c d tail hc hcd hd harg hp ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact le_rfl
    · exact hcd.le.trans (ih e he)

theorem SourcePath.strict {q : Nat} {source path : List Nat} (hp : SourcePath q source path) :
    (path.map (value q)).Pairwise (· < ·) := by
  induction hp with
  | stop c hc hmax => simp only [List.map_cons, List.map_nil, List.pairwise_singleton]
  | next c d tail hc hcd hd harg hp ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact hcd.trans_le (hp.head_le a ha)

theorem SourcePath.end_max {q : Nat} {source path : List Nat} (hp : SourcePath q source path) :
    Node q (endpoint path) ∧ ∀ d ∈ source, value q d ≤ value q (endpoint path) := by
  induction hp with
  | stop c hc hmax => exact ⟨hc, hmax⟩
  | next c d tail hc hcd hd harg hp ih => exact ih

theorem SourcePath.bounded {q : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : SourcePath q source (c :: tail)) (α : Ordinal.{0}) (hc : value q c ≤ α)
    (hs : ∀ d ∈ source, value q d ≤ α) : ∀ d ∈ c :: tail, value q d ≤ α := by
  revert hc
  induction hp with
  | stop c hn hmax => intro hc d hd; rw [List.mem_singleton.mp hd]; exact hc
  | next c d tail hn hcd hd harg hp ih =>
    intro hc e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hc
    · exact ih (hs d hd) e he

theorem endpoint_mem (c : Nat) (tail : List Nat) : endpoint (c :: tail) ∈ c :: tail := by
  induction tail generalizing c with
  | nil => exact List.mem_cons_self
  | cons d tail ih => exact List.mem_cons_of_mem c (ih d)

abbrev rootShape := Hereditary.Localization.rootShape

theorem rootShape_primrec : Primrec rootShape := Hereditary.Localization.rootShape_primrec

theorem rootShape_code (t : RelativeTerm Nat) : rootShape t.code = true ↔ ∃ a, t = .theta 0 a :=
  Hereditary.Localization.rootShape_code t

def inputCheck (q c : Nat) : Bool := Comparison.acceptedCode q c && rootShape c

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp Comparison.acceptedCode_primrec (rootShape_primrec.comp Primrec.snd)).to₂

theorem inputCheck_exact (q c : Nat) : inputCheck q c = true ↔ Node q c := by
  constructor
  · intro h
    have hc := (Comparison.acceptedCode_exact q c).mp (Bool.and_eq_true.mp h).1
    obtain ⟨t, ht, hchecked⟩ := (checkCode_exact q c).mp hc.1
    have hshape : rootShape t.code = true := by rw [ht]; exact (Bool.and_eq_true.mp h).2
    obtain ⟨a, rfl⟩ := (rootShape_code t).mp hshape
    exact ⟨a, ht.symm, hchecked, by simpa only [← ht, rawTree_code, Comparison.Normal] using hc.2⟩
  · intro hc
    apply Bool.and_eq_true.mpr
    refine ⟨node_accepted q c hc, ?_⟩
    obtain ⟨a, rfl, ha, hn⟩ := hc
    exact (rootShape_code _).mpr ⟨a, rfl⟩

def baseRaw (q : Nat) : Nat := SourceChi.Powers.baseTree.code

theorem baseRaw_primrec : Primrec baseRaw := Primrec.const _

theorem baseRaw_node (q : Nat) (hq : baseCheck q = true) : Node q (baseRaw q) :=
  ⟨Normalization.zeroTree, rfl, SourceChi.Powers.baseTree_checked q hq,
    Normalization.zeroTree_normal q⟩

theorem baseRaw_value (q : Nat) (hq : baseCheck q = true) : value q (baseRaw q) = base q := by
  simpa only [baseRaw, value, interpretation_code] using SourceChi.Powers.baseTree_value q hq

theorem baseRaw_le (q c : Nat) (hc : Node q c) : value q (baseRaw q) ≤ value q c := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  rw [baseRaw_value q ((Bool.and_eq_true.mp ha).1), value, interpretation_code]
  simpa only [omegaSequence_zero] using (FixedPoint.checked_theta_range q 0 a ha).1

def nativePath (q c : Nat) : List Nat :=
  walk (support c).length q (baseRaw q) (live q (baseRaw q) (support c))

theorem nativePath_primrec : Primrec₂ nativePath := by
  have hs := support_primrec.comp Primrec.snd
  have hb := baseRaw_primrec.comp Primrec.fst
  have hl := live_primrec.comp (Primrec.fst.pair (hb.pair hs))
  exact (walk_primrec.comp ((Primrec.list_length.comp hs).pair (Primrec.fst.pair (hb.pair hl)))).to₂

theorem nativePath_head (q c : Nat) : ∃ tail : List Nat, nativePath q c = baseRaw q :: tail :=
  walk_head _ _ _ _

theorem nativePath_source (q c : Nat) (hc : inputCheck q c = true) : SourcePath q (support c) (nativePath q c) := by
  have hn := (inputCheck_exact q c).mp hc
  have hq := node_baseCheck q c hn
  have ha : Available q (baseRaw q) (support c) (live q (baseRaw q) (support c)) := by
    intro d
    rw [live_mem]
    constructor
    · rintro ⟨hd, hlt⟩
      exact ⟨hd, (value_less_exact q _ d (baseRaw_node q hq) (support_node q c d hn hd)).mp hlt⟩
    · rintro ⟨hd, hlt⟩
      exact ⟨hd, (value_less_exact q _ d (baseRaw_node q hq) (support_node q c d hn hd)).mpr hlt⟩
  exact walk_source _ _ _ _ _ (baseRaw_node q hq) (fun d hd => support_node q c d hn hd) ha
    (live_length_le q (baseRaw q) (support c))

theorem nativePath_end (q c : Nat) (hc : inputCheck q c = true) : value q (endpoint (nativePath q c)) = value q c := by
  have hn := (inputCheck_exact q c).mp hc
  have hp := nativePath_source q c hc
  have he := hp.end_max
  obtain ⟨tail, ht⟩ := nativePath_head q c
  have hbound : ∀ d ∈ nativePath q c, value q d ≤ value q c := by
    rw [ht] at hp ⊢
    exact hp.bounded _ (baseRaw_le q c hn) (fun d hd => support_bound q c d hn hd)
  have hm : endpoint (nativePath q c) ∈ nativePath q c := by rw [ht]; exact endpoint_mem _ _
  exact le_antisymm (hbound _ hm) (he.2 c (support_root q c hn))

theorem nativePath_nodes (q c : Nat) (hc : inputCheck q c = true) : ∀ d ∈ nativePath q c, Node q d :=
  (nativePath_source q c hc).nodes

theorem nativePath_strict (q c : Nat) (hc : inputCheck q c = true) :
    ((nativePath q c).map (value q)).Pairwise (· < ·) := (nativePath_source q c hc).strict

theorem nativePath_length (q c : Nat) : (nativePath q c).length ≤ (support c).length + 1 := walk_length_le _ _ _ _

theorem sourcePath_tail_mem {q : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : SourcePath q source (c :: tail)) : ∀ d ∈ tail, d ∈ source := by
  induction hp with
  | stop c hc hmax => intro d hd; exact False.elim (List.not_mem_nil hd)
  | next c d tail hc hcd hd harg hp ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hd
    · exact ih e he

theorem sourcePath_head_lt_tail {q : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : SourcePath q source (c :: tail)) : ∀ d ∈ tail, value q c < value q d := by
  have hs := List.pairwise_cons.mp hp.strict
  intro d hd
  exact hs.1 _ (List.mem_map.mpr ⟨d, hd, rfl⟩)

/-- Finite syntax descent, using only the genuine comparison witness and
maximal actual arguments, recovers the selected value in every larger node.
The output need not retain the selected node's literal spelling. -/
theorem selected_value_in_support (q root c : Nat) (hroot : Node q root) (hc : Node q c)
    (hmax : ∀ d ∈ support root, value q c ≤ value q d → argumentValue q d ≤ argumentValue q c)
    (d : Nat) (hd : d ∈ support root) (hcd : value q c ≤ value q d) :
    ∃ e ∈ support d, value q e = value q c := by
  have hall : ∀ n : Nat, ∀ d : Nat, (ThetaCourse.rawTree d).size = n →
      d ∈ support root → value q c ≤ value q d → ∃ e ∈ support d, value q e = value q c := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hsize hd hcd
      have hdn := support_node q root d hroot hd
      by_cases heq : value q c = value q d
      · exact ⟨d, support_root q d hdn, heq.symm⟩
      · have hlt : value q c < value q d := lt_of_le_of_ne hcd heq
        obtain ⟨s, hs, hcs⟩ := reversed_argument_witness q c d hc hdn hlt (hmax d hd hcd)
        have hnest := nested_support_size q d hdn s hs
        have hsr := support_trans q root d s.code hroot hd hnest.1
        have hcsCode : value q c ≤ value q s.code := by
          simpa only [value, interpretation_code] using hcs
        have hsmall : (ThetaCourse.rawTree s.code).size < n := hnest.2.trans_eq hsize
        obtain ⟨e, he, hval⟩ := ih _ hsmall s.code rfl hsr hcsCode
        exact ⟨e, support_trans q d s.code e hdn hnest.1 he, hval⟩
  exact hall _ d rfl hd hcd

/-- Hereditary support for each genuinely selected localization node. -/
theorem sourcePath_selected_support {q root previous c : Nat} {tail : List Nat}
    (hroot : Node q root) (hp : SourcePath q (support root) (previous :: c :: tail)) :
    ∀ d ∈ c :: tail, ∃ e ∈ support d, value q e = value q c := by
  cases hp with
  | next previous c tail hn hpc hcs harg hrest =>
    have hc := hrest.nodes c List.mem_cons_self
    have hmax : ∀ d ∈ support root, value q c ≤ value q d → argumentValue q d ≤ argumentValue q c :=
      fun d hd hcd => harg d hd (hpc.trans_le hcd)
    intro d hd
    have hds : d ∈ support root := by
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hcs
      · exact sourcePath_tail_mem hrest d hd
    exact selected_value_in_support q root c hroot hc hmax d hds (hrest.head_le d hd)

/-- The actual interval clause of source Lemma 2.33(a). The intermediate
theta node may be absent from the original literal support. -/
theorem sourcePath_interval_argument_lt {q root previous d : Nat} {tail : List Nat}
    (hroot : Node q root) (hp : SourcePath q (support root) (previous :: d :: tail))
    (b : Nat) (hb : Node q b) (hpb : value q previous < value q b)
    (hbd : value q b < value q d) : argumentValue q b < argumentValue q d := by
  cases hp with
  | next previous d tail hn hpd hds harg hrest =>
    have hd := hrest.nodes d List.mem_cons_self
    by_contra hnot
    have hdb : argumentValue q d ≤ argumentValue q b := le_of_not_gt hnot
    have hmax : ∀ e ∈ support root, value q b ≤ value q e → argumentValue q e ≤ argumentValue q b :=
      fun e he hbe => (harg e he (hpb.trans_le hbe)).trans hdb
    obtain ⟨e, hed, heb⟩ := selected_value_in_support q root b hroot hb hmax d hds hbd.le
    have hes := support_trans q root d e hroot hds hed
    have hen := support_node q d e hd hed
    have hargument := (node_value_eq_iff_argument_eq q e b hen hb).mp heb
    have hbe : argumentValue q b ≤ argumentValue q d := by
      rw [← hargument]
      apply harg e hes
      rw [heb]
      exact hpb
    have hvalue := (node_value_eq_iff_argument_eq q b d hb hd).mpr (le_antisymm hbe hdb)
    exact hvalue.not_lt hbd


end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization
