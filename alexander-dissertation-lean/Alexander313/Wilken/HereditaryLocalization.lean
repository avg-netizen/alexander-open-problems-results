import Alexander313.Wilken.HereditaryEpsilonOffsets
import Alexander313.Wilken.HereditaryLowering
import Alexander313.Wilken.HereditaryPrincipalSupport

/-!
# Actual finite source localization

The literal support opens full-depth theta-zero syntax, unlike the exposed
finite star list. Its identification with the semantic source P_0 value set
retains the support module's stronger SourceNormal convention.
The next node has value above the current value and greatest actual argument
among all such support nodes. Arguments use the full hereditary comparator;
they need not be low union codes. After a step all nodes with smaller or equal
values are removed, including duplicate spellings. A length bound proves the
actual finite iteration stops. Source root membership and the genuine support
bound identify its endpoint with the root value. This does not prove the fixed
point refinements of Lemma 2.33. All terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Localization

open Theta

/-- A literal admitted normal theta-zero node at the given relative base. -/
def Node (r c : Nat) : Prop := ∃ a : RelativeTerm Nat,
  c = (RelativeTerm.theta 0 a).code ∧ check r (.theta 0 a) = true ∧ Theta.Normal r (.theta 0 a)

def argumentCode (c : Nat) : Nat := (c - 1).unpair.2.unpair.2

theorem argumentCode_primrec : Primrec argumentCode :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
    (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))))

@[simp] theorem argumentCode_theta (a : RelativeTerm Nat) : argumentCode (RelativeTerm.theta 0 a).code = a.code := by
  simp only [argumentCode, code_theta, Nat.succ_sub_one, Nat.unpair_pair]

noncomputable def value (r c : Nat) : Ordinal.{0} := interpretation r c

noncomputable def argumentValue (r c : Nat) : Ordinal.{0} := interpretation r (argumentCode c)

theorem node_low (r c : Nat) (hc : Node r c) : lowCheckCode r c = true := by
  obtain ⟨a, rfl, ha, _⟩ := hc
  simp only [lowCheckCode_code, lowCheck, ha, outerSort, Nat.zero_add,
    le_refl, decide_true, Bool.true_and]

theorem node_normal (r c : Nat) (hc : Node r c) : Theta.Normal r (ThetaCourse.rawTree c) := by
  obtain ⟨a, rfl, _, ha⟩ := hc
  simpa only [ThetaCourse.rawTree_code] using ha

theorem node_argument (r c : Nat) (hc : Node r c) :
    checkCode r (argumentCode c) = true ∧ Theta.Normal r (ThetaCourse.rawTree (argumentCode c)) := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  obtain ⟨n, ht⟩ := (check_iff_finite_admissible r (.theta 0 a)).mp ha
  have hac := admitted_checked (admitted_theta_argument ht)
  simpa only [argumentCode_theta, checkCode_code, ThetaCourse.rawTree_code] using
    And.intro hac ((normal_theta r 0 a).mp hn)

theorem value_less_exact (r c d : Nat) (hc : Node r c) (hd : Node r d) :
    Theta.lessCode r c d = true ↔ value r c < value r d := by
  obtain ⟨a, rfl, ha, hna⟩ := hc
  obtain ⟨b, rfl, hb, hnb⟩ := hd
  simpa only [Theta.lessCode_code, value, interpretation_code] using
    Theta.less_correct r (.theta 0 a) (.theta 0 b) ha hb hna hnb

theorem argument_less_exact (r c d : Nat) (hc : Node r c) (hd : Node r d) :
    Theta.lessCode r (argumentCode c) (argumentCode d) = true ↔ argumentValue r c < argumentValue r d := by
  obtain ⟨a, rfl, ha, hna⟩ := hc
  obtain ⟨b, rfl, hb, hnb⟩ := hd
  obtain ⟨n, hat⟩ := (check_iff_finite_admissible r (.theta 0 a)).mp ha
  obtain ⟨m, hbt⟩ := (check_iff_finite_admissible r (.theta 0 b)).mp hb
  simpa only [argumentCode_theta, Theta.lessCode_code, argumentValue, interpretation_code] using
    Theta.less_correct r a b (admitted_checked (admitted_theta_argument hat))
      (admitted_checked (admitted_theta_argument hbt))
      ((normal_theta r 0 a).mp hna) ((normal_theta r 0 b).mp hnb)

def choose (r c : Nat) (tail : Option Nat) : Option Nat :=
  match tail with
  | none => some c
  | some d => some (cond (Theta.lessCode r (argumentCode d) (argumentCode c)) c d)

theorem choose_primrec : Primrec (fun p : Nat × (Nat × Option Nat) => choose p.1 p.2.1 p.2.2) := by
  have ho : Primrec (fun p : Nat × (Nat × Option Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hc : Primrec (fun p : Nat × (Nat × Option Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun p : (Nat × (Nat × Option Nat)) × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hcan : Primrec (fun p : (Nat × (Nat × Option Nat)) × Nat => p.1.2.1) :=
    hc.comp Primrec.fst
  have ht := Theta.Effective.lessCode_primrec.comp
    (hr.pair ((argumentCode_primrec.comp Primrec.snd).pair (argumentCode_primrec.comp hcan)))
  have h := Primrec.option_casesOn ho (Primrec.option_some.comp hc)
    (Primrec.option_some.comp (Primrec.cond ht hcan Primrec.snd)).to₂
  apply h.of_eq
  intro p
  cases p.2.2 <;> rfl

def best (r : Nat) : List Nat → Option Nat
  | [] => none
  | c :: cs => choose r c (best r cs)

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

theorem best_none (r : Nat) (xs : List Nat) : best r xs = none ↔ xs = [] := by
  cases xs with
  | nil => simp only [best]
  | cons c cs => cases h : best r cs <;> simp [best, h, choose]

theorem best_mem (r : Nat) (xs : List Nat) (c : Nat) (hc : best r xs = some c) : c ∈ xs := by
  induction xs generalizing c with
  | nil => simp only [best, reduceCtorEq] at hc
  | cons a xs ih =>
    cases ht : best r xs with
    | none => have he : a = c := by simpa only [best, ht, choose, Option.some.injEq] using hc
              rw [← he]; exact List.mem_cons_self
    | some d =>
      cases hl : Theta.lessCode r (argumentCode d) (argumentCode a) with
      | false =>
        have he : d = c := by simpa only [best, ht, choose, hl, Bool.cond_false, Option.some.injEq] using hc
        rw [← he]; exact List.mem_cons_of_mem _ (ih d ht)
      | true =>
        have he : a = c := by simpa only [best, ht, choose, hl, Bool.cond_true, Option.some.injEq] using hc
        rw [← he]; exact List.mem_cons_self

theorem best_maximal (r : Nat) (xs : List Nat) (hx : ∀ c ∈ xs, Node r c)
    (c : Nat) (hc : best r xs = some c) : ∀ d ∈ xs, argumentValue r d ≤ argumentValue r c := by
  revert hx c hc
  induction xs with
  | nil => intro _ c hc; simp only [best, reduceCtorEq] at hc
  | cons a xs ih =>
    intro hx c hc
    have ha := hx a List.mem_cons_self
    have htail := fun d hd => hx d (List.mem_cons_of_mem _ hd)
    cases ht : best r xs with
    | none =>
      have hxnil := (best_none r xs).mp ht
      subst xs
      have he : a = c := by simpa only [best, choose, Option.some.injEq] using hc
      subst c
      intro d hd
      have he := List.mem_singleton.mp hd
      rw [he]
    | some b =>
      have hb := htail b (best_mem r xs b ht)
      have hm := ih htail b ht
      cases hl : Theta.lessCode r (argumentCode b) (argumentCode a) with
      | false =>
        have he : b = c := by simpa only [best, ht, choose, hl, Bool.cond_false, Option.some.injEq] using hc
        subst c
        have hab : argumentValue r a ≤ argumentValue r b := le_of_not_gt (fun h => by
          have hh := (argument_less_exact r b a hb ha).mpr h
          simp only [hl, Bool.false_eq_true] at hh)
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hab
        · exact hm d hd
      | true =>
        have he : a = c := by simpa only [best, ht, choose, hl, Bool.cond_true, Option.some.injEq] using hc
        subst c
        have hba := (argument_less_exact r b a hb ha).mp hl
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact le_rfl
        · exact (hm d hd).trans hba.le

/-- Remove every node whose value is at most the new current value. -/
def live (r current : Nat) : List Nat → List Nat
  | [] => []
  | c :: cs => cond (Theta.lessCode r current c) (c :: live r current cs) (live r current cs)

theorem live_primrec : Primrec (fun p : Nat × (Nat × List Nat) => live p.1 p.2.1 p.2.2) := by
  have hr : Primrec (fun p : (Nat × (Nat × List Nat)) × (Nat × List Nat) => p.1.1) := Primrec.fst.comp Primrec.fst
  have hcur : Primrec (fun p : (Nat × (Nat × List Nat)) × (Nat × List Nat) => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hc : Primrec (fun p : (Nat × (Nat × List Nat)) × (Nat × List Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have htail : Primrec (fun p : (Nat × (Nat × List Nat)) × (Nat × List Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have ht := Theta.Effective.lessCode_primrec.comp (hr.pair (hcur.pair hc))
  have hs : Primrec₂ (fun (p : Nat × (Nat × List Nat)) (s : Nat × List Nat) =>
      cond (Theta.lessCode p.1 p.2.1 s.1) (s.1 :: s.2) s.2) := by
    exact (Primrec.cond ht (Primrec.list_cons.comp hc htail) htail).to₂
  have h := Primrec.list_foldr (Primrec.snd.comp Primrec.snd) (Primrec.const []) hs
  have he : (fun p : Nat × (Nat × List Nat) => p.2.2.foldr
      (fun c xs => cond (Theta.lessCode p.1 p.2.1 c) (c :: xs) xs) []) =
        fun p => live p.1 p.2.1 p.2.2 := by
    funext p
    induction p.2.2 with
    | nil => rfl
    | cons c cs ih => simp only [List.foldr_cons, live, ih]
  rw [he] at h
  exact h

theorem live_mem (r current : Nat) (xs : List Nat) (c : Nat) :
    c ∈ live r current xs ↔ c ∈ xs ∧ Theta.lessCode r current c = true := by
  induction xs with
  | nil => simp only [live, List.not_mem_nil, false_and]
  | cons a xs ih =>
    cases ht : Theta.lessCode r current a with
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

theorem live_length_le (r current : Nat) (xs : List Nat) : (live r current xs).length ≤ xs.length := by
  induction xs with
  | nil => exact le_rfl
  | cons a xs ih => cases ht : Theta.lessCode r current a <;> simp only [live, ht,
      Bool.cond_false, Bool.cond_true, List.length_cons] <;> omega

theorem live_length_lt (r current : Nat) (xs : List Nat) (c : Nat) (hc : c ∈ xs)
    (hfalse : Theta.lessCode r current c = false) : (live r current xs).length < xs.length := by
  revert hc
  induction xs with
  | nil => intro hc; exact False.elim (List.not_mem_nil hc)
  | cons a xs ih =>
    intro hc
    rcases List.mem_cons.mp hc with he | hc
    · subst a
      simpa only [live, hfalse, Bool.cond_false, List.length_cons] using
        Nat.lt_succ_of_le (live_length_le r current xs)
    · have ht := ih hc
      cases hl : Theta.lessCode r current a <;> simp only [live, hl,
        Bool.cond_false, Bool.cond_true, List.length_cons] <;> omega

abbrev State := (Nat × List Nat) × List Nat

/-- The last component records earlier values in chronological order. -/
def step (r : Nat) (s : State) : State :=
  match best r s.1.2 with
  | none => s
  | some c => ((c, live r c s.1.2), s.2 ++ [s.1.1])

theorem step_primrec : Primrec₂ step := by
  have hr : Primrec (fun p : (Nat × State) × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun p : (Nat × State) × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have hxs := Primrec.snd.comp (Primrec.fst.comp hs)
  have hcur := Primrec.fst.comp (Primrec.fst.comp hs)
  have hout := Primrec.snd.comp hs
  have hl := live_primrec.comp (hr.pair (Primrec.snd.pair hxs))
  have hb : Primrec (fun p : Nat × State => best p.1 p.2.1.2) :=
    best_primrec.comp Primrec.fst (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hnew := (Primrec.snd.pair hl).pair (Primrec.list_concat.comp hout hcur)
  have h := (Primrec.option_casesOn hb Primrec.snd hnew.to₂).to₂
  apply h.of_eq
  intro r s
  simp only [step]
  cases best r s.1.2 <;> rfl

def iterate (r : Nat) : Nat → State → State
  | 0, s => s
  | n + 1, s => step r (iterate r n s)

theorem iterate_primrec : Primrec₂ (fun p : Nat × State => fun n : Nat => iterate p.1 n p.2) := by
  have init : Primrec (fun p : Nat × State => p.2) := Primrec.snd
  have next : Primrec₂ (fun p : Nat × State => fun s : Nat × State => step p.1 s.2) :=
    (step_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.nat_rec init next
  apply h.of_eq
  intro p n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (step p.1) ih

theorem iterate_succ_start (r n : Nat) (s : State) : iterate r (n + 1) s = iterate r n (step r s) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (step r) ih

def addPrefix (p : List Nat) (s : State) : State := (s.1, p ++ s.2)

theorem step_addPrefix (r : Nat) (p : List Nat) (s : State) : step r (addPrefix p s) = addPrefix p (step r s) := by
  cases hb : best r s.1.2 <;> simp only [step, addPrefix, hb, List.append_assoc]

theorem iterate_addPrefix (r n : Nat) (p : List Nat) (s : State) :
    iterate r n (addPrefix p s) = addPrefix p (iterate r n s) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate, ih, step_addPrefix]; rfl

def finish (s : State) : List Nat := s.2 ++ [s.1.1]

def walk (fuel r current : Nat) (xs : List Nat) : List Nat :=
  finish (iterate r fuel ((current, xs), []))

theorem walk_zero (r current : Nat) (xs : List Nat) : walk 0 r current xs = [current] := rfl

theorem walk_succ (n r current : Nat) (xs : List Nat) : walk (n + 1) r current xs =
    match best r xs with
    | none => [current]
    | some c => current :: walk n r c (live r c xs) := by
  rw [walk, iterate_succ_start]
  cases hb : best r xs with
  | none =>
    have hs : step r ((current, xs), []) = ((current, xs), []) := by simp only [step, hb]
    have hi : iterate r n ((current, xs), []) = ((current, xs), []) := by
      induction n with
      | zero => rfl
      | succ n ih => rw [iterate, ih, hs]
    simp only [step, hb, hi, finish, List.nil_append]
  | some c =>
    have hs : step r ((current, xs), []) = addPrefix [current] ((c, live r c xs), []) := by
      simp only [step, hb, addPrefix, List.nil_append, List.append_nil]
    rw [hs, iterate_addPrefix]
    simp only [finish, addPrefix, walk, List.cons_append, List.nil_append, List.append_assoc]

/-- The exact surviving support after the current value has been reached. -/
def Available (r current : Nat) (source xs : List Nat) : Prop :=
  ∀ c, c ∈ xs ↔ c ∈ source ∧ value r current < value r c

/-- Literal source recurrence, greatest argument, and absence of a further step. -/
inductive SourcePath (r : Nat) (source : List Nat) : List Nat → Prop
  | stop (c : Nat) (hc : Node r c) (hmax : ∀ d ∈ source, value r d ≤ value r c) : SourcePath r source [c]
  | next (c d : Nat) (tail : List Nat) (hc : Node r c) (hcd : value r c < value r d)
      (hd : d ∈ source) (harg : ∀ e ∈ source, value r c < value r e → argumentValue r e ≤ argumentValue r d)
      (hrest : SourcePath r source (d :: tail)) : SourcePath r source (c :: d :: tail)

theorem walk_head (fuel r current : Nat) (xs : List Nat) :
    ∃ tail : List Nat, walk fuel r current xs = current :: tail := by
  induction fuel generalizing current xs with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    rw [walk_succ]
    cases best r xs with
    | none => exact ⟨[], rfl⟩
    | some c => exact ⟨walk n r c (live r c xs), rfl⟩

theorem walk_source (fuel r current : Nat) (source xs : List Nat)
    (hcur : Node r current) (hs : ∀ c ∈ source, Node r c)
    (ha : Available r current source xs) (hbudget : xs.length ≤ fuel) :
    SourcePath r source (walk fuel r current xs) := by
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
    cases hb : best r xs with
    | none =>
      apply SourcePath.stop current hcur
      intro d hd
      apply le_of_not_gt
      intro hlt
      have hm := (ha d).mpr ⟨hd, hlt⟩
      rw [(best_none r xs).mp hb] at hm
      exact List.not_mem_nil hm
    | some c =>
      have hcx := best_mem r xs c hb
      have hcs := (ha c).mp hcx
      have hcn := hs c hcs.1
      have hnodes : ∀ d ∈ xs, Node r d := fun d hd => hs d ((ha d).mp hd).1
      have hself : Theta.lessCode r c c = false := Bool.eq_false_of_not_eq_true
        (fun h => (lt_irrefl (value r c)) ((value_less_exact r c c hcn hcn).mp h))
      have hsmall := live_length_lt r c xs c hcx hself
      have hnext : Available r c source (live r c xs) := by
        intro d
        rw [live_mem]
        constructor
        · rintro ⟨hd, hlt⟩
          exact ⟨((ha d).mp hd).1, (value_less_exact r c d hcn (hnodes d hd)).mp hlt⟩
        · rintro ⟨hd, hlt⟩
          have hdx := (ha d).mpr ⟨hd, hcs.2.trans hlt⟩
          exact ⟨hdx, (value_less_exact r c d hcn (hs d hd)).mpr hlt⟩
      have hbound : (live r c xs).length ≤ n := by omega
      have hpath := ih c (live r c xs) hcn hnext hbound
      obtain ⟨tail, he⟩ := walk_head n r c (live r c xs)
      change SourcePath r source (current :: walk n r c (live r c xs))
      rw [he] at hpath ⊢
      exact SourcePath.next current c tail hcur hcs.2 hcs.1
        (fun d hd hlt => best_maximal r xs hnodes c hb d ((ha d).mpr ⟨hd, hlt⟩)) hpath

theorem finish_primrec : Primrec finish :=
  Primrec.list_concat.comp Primrec.snd (Primrec.fst.comp Primrec.fst)

theorem walk_primrec : Primrec (fun p : Nat × (Nat × (Nat × List Nat)) =>
    walk p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hr : Primrec (fun p : Nat × (Nat × (Nat × List Nat)) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : Nat × (Nat × (Nat × List Nat)) => ((p.2.2.1, p.2.2.2), ([] : List Nat))) :=
    (Primrec.snd.comp Primrec.snd).pair (Primrec.const [])
  exact finish_primrec.comp (iterate_primrec.comp (hr.pair hi) Primrec.fst)

theorem walk_length_le (fuel r current : Nat) (xs : List Nat) : (walk fuel r current xs).length ≤ fuel + 1 := by
  induction fuel generalizing current xs with
  | zero => exact le_rfl
  | succ n ih =>
    rw [walk_succ]
    cases best r xs with
    | none => simp only [List.length_singleton]; omega
    | some c => simpa only [List.length_cons] using Nat.succ_le_succ (ih c (live r c xs))

/-- The endpoint of a literal nonempty sequence, with an auxiliary empty default. -/
def endpoint : List Nat → Nat
  | [] => 0
  | [c] => c
  | _ :: d :: tail => endpoint (d :: tail)

theorem SourcePath.nodes {r : Nat} {source path : List Nat} (hp : SourcePath r source path) :
    ∀ c ∈ path, Node r c := by
  induction hp with
  | stop c hc hmax => intro d hd; rw [List.mem_singleton.mp hd]; exact hc
  | next c d tail hc hcd hd harg hp ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hc
    · exact ih e he

theorem SourcePath.head_le {r : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : SourcePath r source (c :: tail)) : ∀ d ∈ c :: tail, value r c ≤ value r d := by
  induction tail generalizing c with
  | nil => intro d hd; rw [List.mem_singleton.mp hd]
  | cons d tail ih =>
    cases hp with
    | next c d tail hc hcd hd harg hrest =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact le_rfl
      · exact hcd.le.trans (ih hrest e he)

theorem SourcePath.strict {r : Nat} {source path : List Nat} (hp : SourcePath r source path) :
    (path.map (value r)).Pairwise (· < ·) := by
  induction hp with
  | stop c hc hmax => simp only [List.map_cons, List.map_nil, List.pairwise_singleton]
  | next c d tail hc hcd hd harg hp ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact hcd.trans_le (hp.head_le a ha)

theorem SourcePath.end_max {r : Nat} {source path : List Nat} (hp : SourcePath r source path) :
    Node r (endpoint path) ∧ ∀ d ∈ source, value r d ≤ value r (endpoint path) := by
  induction hp with
  | stop c hc hmax => exact ⟨hc, hmax⟩
  | next c d tail hc hcd hd harg hp ih => exact ih

theorem SourcePath.bounded {r : Nat} {source : List Nat} {c : Nat} {tail : List Nat}
    (hp : SourcePath r source (c :: tail)) (α : Ordinal.{0}) (hc : value r c ≤ α)
    (hs : ∀ d ∈ source, value r d ≤ α) : ∀ d ∈ c :: tail, value r d ≤ α := by
  induction tail generalizing c with
  | nil => intro d hd; rw [List.mem_singleton.mp hd]; exact hc
  | cons d tail ih =>
    cases hp with
    | next c d tail hn hcd hd harg hrest =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hc
      · exact ih hrest (hs d hd) e he

theorem endpoint_mem (c : Nat) (tail : List Nat) : endpoint (c :: tail) ∈ c :: tail := by
  induction tail generalizing c with
  | nil => exact List.mem_cons_self
  | cons d tail ih => exact List.mem_cons_of_mem c (ih d)

/-- The guard retains both original admission/normality and literal root shape. -/
def rootShape (c : Nat) : Bool :=
  !(c == 0) && ((c - 1).unpair.1 == 2) && ((c - 1).unpair.2.unpair.1 == 0)

theorem rootShape_primrec : Primrec rootShape := by
  have hraw := Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))
  exact Primrec.and.comp
    (Primrec.and.comp (Primrec.not.comp (Primrec.beq.comp Primrec.id (Primrec.const 0)))
      (Primrec.beq.comp (Primrec.fst.comp hraw) (Primrec.const 2)))
    (Primrec.beq.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp hraw))) (Primrec.const 0))

theorem rootShape_code (t : RelativeTerm Nat) : rootShape t.code = true ↔ ∃ a, t = .theta 0 a := by
  cases t with
  | parameter p => simp [rootShape, code, Nat.unpair_pair]
  | sum a b => simp [rootShape, code, Nat.unpair_pair]
  | theta k a => simp [rootShape, code, Nat.unpair_pair]

def inputCheck (r c : Nat) : Bool := Theta.acceptedLowCode r c && rootShape c

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp Theta.Effective.acceptedLowCode_primrec (rootShape_primrec.comp Primrec.snd)).to₂

theorem inputCheck_exact (r c : Nat) : inputCheck r c = true ↔ Node r c := by
  constructor
  · intro h
    have hc := (Theta.acceptedLowCode_iff r c).mp (Bool.and_eq_true_iff.mp h).1
    obtain ⟨t, ht, hlow⟩ := (lowCheckCode_iff r c).mp hc.1
    have hshape : rootShape t.code = true := by rw [ht]; exact (Bool.and_eq_true_iff.mp h).2
    obtain ⟨a, rfl⟩ := (rootShape_code t).mp hshape
    exact ⟨a, ht.symm, (Bool.and_eq_true_iff.mp hlow).1,
      by simpa only [← ht, ThetaCourse.rawTree_code] using hc.2⟩
  · intro hc
    apply Bool.and_eq_true_iff.mpr
    refine ⟨(Theta.acceptedLowCode_iff r c).mpr ⟨node_low r c hc, node_normal r c hc⟩, ?_⟩
    obtain ⟨a, rfl, _, _⟩ := hc
    exact (rootShape_code _).mpr ⟨a, rfl⟩

def baseRaw (r : Nat) : Nat := (RelativeTerm.theta 0 (zeroTree r)).code

theorem baseRaw_primrec : Primrec baseRaw :=
  code_primrec.comp (theta_primrec.comp (Primrec.const 0) Normalization.Effective.zeroTree_primrec)

theorem baseRaw_node (r : Nat) : Node r (baseRaw r) := by
  have hlow := EpsilonOffsets.baseCode_checked r
  have hc : lowCheckCode r (baseRaw r) = true := by
    simpa only [EpsilonOffsets.baseCode, unionCheck, Nat.unpair_pair, baseRaw] using hlow
  refine ⟨zeroTree r, rfl, ?_, ?_⟩
  · exact (Bool.and_eq_true_iff.mp (by simpa only [baseRaw, lowCheckCode_code, lowCheck] using hc)).1
  · exact (normal_theta r 0 _).mpr (Normalization.zeroTree_normal r)

theorem baseRaw_value (r : Nat) : value r (baseRaw r) = finiteBase r := by
  simpa only [EpsilonOffsets.baseCode, unionInterpretation, Nat.unpair_pair, baseRaw, value] using
    EpsilonOffsets.baseCode_value r

theorem baseRaw_le (r c : Nat) (hc : Node r c) : value r (baseRaw r) ≤ value r c := by
  obtain ⟨a, rfl, ha, _⟩ := hc
  rw [baseRaw_value, value, interpretation_code]
  exact Lowering.checked_theta_base_le r 0 a ha

/-- Full P_0 traversal; parameters remain atomic at this relative base. -/
def support (c : Nat) : List Nat := PrincipalSupport.listCode 0 c

theorem support_primrec : Primrec support := PrincipalSupport.listCode_primrec.comp (Primrec.const 0) Primrec.id

theorem support_node (r c d : Nat) (hc : Node r c) (hd : d ∈ support c) : Node r d := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  rw [support, PrincipalSupport.listCode_code] at hd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hd
  obtain ⟨b, rfl⟩ := PrincipalSupport.principalList_shape 0 (.theta 0 a) s hs
  have hb := PrincipalSupport.principalList_node ha hn hs
  exact ⟨b, rfl, hb⟩

theorem support_root (r c : Nat) (hc : Node r c) : c ∈ support c := by
  obtain ⟨a, rfl, _, _⟩ := hc
  rw [support, PrincipalSupport.listCode_code]
  exact List.mem_map.mpr ⟨.theta 0 a, PrincipalSupport.principalList_root 0 a, rfl⟩

theorem support_bound (r c d : Nat) (hc : Node r c) (hd : d ∈ support c) : value r d ≤ value r c := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  rw [support, PrincipalSupport.listCode_code] at hd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hd
  simpa only [value, interpretation_code] using PrincipalSupport.principalList_theta_value_le r a s ha hn hs

def nativePath (r c : Nat) : List Nat :=
  walk (support c).length r (baseRaw r) (live r (baseRaw r) (support c))

theorem nativePath_primrec : Primrec₂ nativePath := by
  have hs : Primrec (fun p : Nat × Nat => support p.2) := support_primrec.comp Primrec.snd
  have hb : Primrec (fun p : Nat × Nat => baseRaw p.1) := baseRaw_primrec.comp Primrec.fst
  have hl := live_primrec.comp (Primrec.fst.pair (hb.pair hs))
  exact (walk_primrec.comp ((Primrec.list_length.comp hs).pair (Primrec.fst.pair (hb.pair hl)))).to₂

theorem nativePath_head (r c : Nat) : ∃ tail : List Nat, nativePath r c = baseRaw r :: tail :=
  walk_head _ _ _ _

theorem nativePath_source (r c : Nat) (hc : inputCheck r c = true) : SourcePath r (support c) (nativePath r c) := by
  have hn := (inputCheck_exact r c).mp hc
  have ha : Available r (baseRaw r) (support c) (live r (baseRaw r) (support c)) := by
    intro d
    rw [live_mem]
    constructor
    · rintro ⟨hd, hlt⟩
      exact ⟨hd, (value_less_exact r _ d (baseRaw_node r) (support_node r c d hn hd)).mp hlt⟩
    · rintro ⟨hd, hlt⟩
      exact ⟨hd, (value_less_exact r _ d (baseRaw_node r) (support_node r c d hn hd)).mpr hlt⟩
  exact walk_source _ _ _ _ _ (baseRaw_node r) (fun d hd => support_node r c d hn hd) ha
    (live_length_le r (baseRaw r) (support c))

theorem nativePath_end (r c : Nat) (hc : inputCheck r c = true) : value r (endpoint (nativePath r c)) = value r c := by
  have hn := (inputCheck_exact r c).mp hc
  have hp := nativePath_source r c hc
  have he := hp.end_max
  obtain ⟨tail, ht⟩ := nativePath_head r c
  have hbound : ∀ d ∈ nativePath r c, value r d ≤ value r c := by
    rw [ht] at hp ⊢
    exact hp.bounded _ (baseRaw_le r c hn) (fun d hd => support_bound r c d hn hd)
  have hm : endpoint (nativePath r c) ∈ nativePath r c := by rw [ht]; exact endpoint_mem _ _
  exact le_antisymm (hbound _ hm) (he.2 c (support_root r c hn))

theorem nativePath_nodes (r c : Nat) (hc : inputCheck r c = true) : ∀ d ∈ nativePath r c, Node r d :=
  (nativePath_source r c hc).nodes

theorem nativePath_strict (r c : Nat) (hc : inputCheck r c = true) :
    ((nativePath r c).map (value r)).Pairwise (· < ·) := (nativePath_source r c hc).strict

theorem nativePath_length (r c : Nat) : (nativePath r c).length ≤ (support c).length + 1 := walk_length_le _ _ _ _

/-- Canonical emission does not assume unique native spelling or source P invariance. -/
def emit (r d : Nat) : Nat := Canonical.canonicalize (Nat.pair r d)

theorem emit_primrec : Primrec₂ emit :=
  (Canonical.Effective.canonicalize_primrec.comp Primrec₂.natPair).to₂

theorem emit_spec (r d : Nat) (hd : Node r d) :
    Canonical.check (emit r d) = true ∧ unionInterpretation (emit r d) = value r d := by
  have hu : unionCheck (Nat.pair r d) = true := by simpa only [unionCheck_pair] using node_low r d hd
  exact ⟨Canonical.canonicalize_check _ hu,
    (Canonical.canonicalize_value _ hu).trans (by simp only [unionInterpretation_pair, value])⟩

def word (r c : Nat) : List Nat := (nativePath r c).map (emit r)

theorem word_primrec : Primrec₂ word := by
  have he : Primrec₂ (fun p : Nat × Nat => fun d : Nat => emit p.1 d) :=
    (emit_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_map nativePath_primrec he).to₂

theorem word_checked (r c : Nat) (hc : inputCheck r c = true) : ∀ d ∈ word r c, Canonical.check d = true := by
  intro d hd
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
  exact (emit_spec r a (nativePath_nodes r c hc a ha)).1

theorem word_values (r c : Nat) (hc : inputCheck r c = true) :
    (word r c).map unionInterpretation = (nativePath r c).map (value r) := by
  simp only [word, List.map_map]
  apply List.map_congr_left
  intro d hd
  exact (emit_spec r d (nativePath_nodes r c hc d hd)).2

theorem word_strict (r c : Nat) (hc : inputCheck r c = true) :
    ((word r c).map unionInterpretation).Pairwise (· < ·) := by
  rw [word_values r c hc]
  exact nativePath_strict r c hc

theorem word_start (r c : Nat) (hc : inputCheck r c = true) :
    ∃ tail : List Nat, word r c = emit r (baseRaw r) :: tail ∧ unionInterpretation (emit r (baseRaw r)) = finiteBase r := by
  obtain ⟨tail, ht⟩ := nativePath_head r c
  exact ⟨tail.map (emit r), by rw [word, ht]; rfl, (emit_spec r _ (baseRaw_node r)).2.trans (baseRaw_value r)⟩

theorem word_length (r c : Nat) : (word r c).length ≤ (support c).length + 1 := by
  simpa only [word, List.length_map] using nativePath_length r c

private theorem endpoint_map (f : Nat → Nat) (c : Nat) (tail : List Nat) :
    endpoint ((c :: tail).map f) = f (endpoint (c :: tail)) := by
  induction tail generalizing c with
  | nil => rfl
  | cons d tail ih => exact ih d

theorem word_end (r c : Nat) (hc : inputCheck r c = true) :
    unionInterpretation (endpoint (word r c)) = value r c := by
  obtain ⟨tail, ht⟩ := nativePath_head r c
  have hn := (nativePath_source r c hc).end_max.1
  have he : endpoint (word r c) = emit r (endpoint (nativePath r c)) := by
    rw [word, ht, endpoint_map]
  rw [he]
  exact (emit_spec r _ hn).2.trans (nativePath_end r c hc)

def encodeWord (r c : Nat) : Nat := Encodable.encode (word r c)

theorem encodeWord_primrec : Primrec₂ encodeWord := (Primrec.encode.comp word_primrec).to₂

def localization (r c : Nat) : Part Nat := cond (inputCheck r c) (Part.some (encodeWord r c)) Part.none

theorem localization_partrec : Partrec₂ localization :=
  (Partrec.cond inputCheck_primrec.to_comp encodeWord_primrec.to_comp.partrec Partrec.none).to₂

theorem localization_domain (r c : Nat) : (localization r c).Dom ↔ Node r c := by
  rw [← inputCheck_exact]
  cases h : inputCheck r c <;> simp [localization, h]

/-- The complete graph of the actual finite algorithm, on its original root domain. -/
def graph (r c output : Nat) : Bool := inputCheck r c && (output == encodeWord r c)

theorem graph_primrec : Primrec (fun p : (Nat × Nat) × Nat => graph p.1.1 p.1.2 p.2) :=
  Primrec.and.comp (inputCheck_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
    (Primrec.beq.comp Primrec.snd (encodeWord_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)))

theorem graph_exact (r c output : Nat) : graph r c output = true ↔
    Node r c ∧ output = Encodable.encode (word r c) := by
  simp only [graph, Bool.and_eq_true, beq_iff_eq, inputCheck_exact, encodeWord]

theorem localization_graph_iff (r c output : Nat) : output ∈ localization r c ↔ graph r c output = true := by
  cases h : inputCheck r c <;> simp [localization, graph, h, Part.mem_some_iff]

theorem localization_returns (r c : Nat) (hc : inputCheck r c = true) :
    Encodable.encode (word r c) ∈ localization r c := by
  simp only [localization, hc, Bool.cond_true, encodeWord, Part.mem_some_iff]

theorem localization_unique (r c : Nat) (hc : inputCheck r c = true) : ∃! output, output ∈ localization r c := by
  refine ⟨Encodable.encode (word r c), localization_returns r c hc, ?_⟩
  intro output hout
  exact ((graph_exact r c output).mp ((localization_graph_iff r c output).mp hout)).2

theorem localization_source (r c output : Nat) (hc : output ∈ localization r c) :
    ∃ path : List Nat, SourcePath r (support c) path ∧ value r (endpoint path) = value r c ∧
      output = Encodable.encode (path.map (emit r)) ∧
      (∀ d ∈ path, Node r d) ∧ ((path.map (value r)).Pairwise (· < ·)) := by
  have hs := (graph_exact r c output).mp ((localization_graph_iff r c output).mp hc)
  have hi := (inputCheck_exact r c).mpr hs.1
  exact ⟨nativePath r c, nativePath_source r c hi, nativePath_end r c hi,
    hs.2, nativePath_nodes r c hi, nativePath_strict r c hi⟩

theorem localization_word (r c : Nat) (rs : List Nat) (hr : Encodable.encode rs ∈ localization r c) :
    rs = word r c ∧ (∀ d ∈ rs, Canonical.check d = true) ∧
      ((rs.map unionInterpretation).Pairwise (· < ·)) ∧ rs.length ≤ (support c).length + 1 := by
  have hs := (graph_exact r c _).mp ((localization_graph_iff r c _).mp hr)
  have he : rs = word r c := Encodable.encode_injective hs.2
  have hi := (inputCheck_exact r c).mpr hs.1
  refine ⟨he, ?_⟩
  rw [he]
  exact ⟨word_checked r c hi, word_strict r c hi, word_length r c⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.Localization
