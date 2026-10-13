import Alexander313.Wilken.AdditiveNormalForm
import Mathlib.Computability.Primrec.List

/-!
# Source dotted right subtraction by genuine finite ANF suffix matching

The source operation a dotminus b returns zero when a<=b. Otherwise it
returns the LEAST ordinal g satisfying a=g+b, or a when no such g exists.
This is distinct from Mathlib's ordinal subtraction (left removal).

Actual normalization of ANF(g)++ANF(b) always retains ANF(b) as a suffix,
with a prefix whose sum is <=g. This derives both suffix necessity and
minimality over ALL ordinals, without assuming left-addition strictness.
The generic matcher is an actual finite PR fold once atom equality is PR.
Its ordinal instance is mathematical; the native caller executes the real
numeric comparator and derives the same result. Uncompiled candidates.
-/

namespace Alexander313.Wilken.OrdinalRightSubtraction

universe u

def prefixMatch {α : Type*} (equal : α → α → Bool) : List α → List α → List α × Bool
  | as, [] => (as, true)
  | [], _ :: _ => ([], false)
  | a :: as, b :: bs => cond (equal a b) (prefixMatch equal as bs) (a :: as, false)

def suffixMatch {α : Type*} (equal : α → α → Bool) (as bs : List α) : List α × Bool :=
  let p := prefixMatch equal as.reverse bs.reverse
  (p.1.reverse, p.2)

theorem prefixMatch_remaining {α : Type*} (equal : α → α → Bool) (as bs : List α) :
    ∃ before, as = before ++ (prefixMatch equal as bs).1 := by
  induction bs generalizing as with
  | nil => exact ⟨[], by cases as <;> rfl⟩
  | cons b bs ih =>
    cases as with
    | nil => exact ⟨[], rfl⟩
    | cons a as =>
      cases he : equal a b with
      | false => exact ⟨[], by simp only [prefixMatch, he, Bool.cond_false, List.nil_append]⟩
      | true =>
        obtain ⟨before, hb⟩ := ih as
        exact ⟨a :: before, by simpa only [prefixMatch, he, Bool.cond_true, List.cons_append] using congrArg (List.cons a) hb⟩

theorem suffixMatch_prefix {α : Type*} (equal : α → α → Bool) (as bs : List α) :
    ∃ after, as = (suffixMatch equal as bs).1 ++ after := by
  obtain ⟨before, hb⟩ := prefixMatch_remaining equal as.reverse bs.reverse
  exact ⟨before.reverse, by simpa only [suffixMatch, List.reverse_reverse, List.reverse_append] using congrArg List.reverse hb⟩

theorem suffixMatch_mem {α : Type*} (equal : α → α → Bool) (as bs : List α) (a : α)
    (ha : a ∈ (suffixMatch equal as bs).1) : a ∈ as := by
  obtain ⟨after, he⟩ := suffixMatch_prefix equal as bs
  rw [he]
  exact List.mem_append.mpr (Or.inl ha)

theorem prefixMatch_exact {α : Type*} [DecidableEq α] (as bs pre : List α) :
    prefixMatch (fun a b => decide (a = b)) as bs = (pre, true) ↔ as = bs ++ pre := by
  induction bs generalizing as pre with
  | nil => simp [prefixMatch]
  | cons b bs ih =>
    cases as with
    | nil => simp [prefixMatch]
    | cons a as =>
      by_cases he : a = b
      · subst a
        simpa [prefixMatch] using ih as pre
      · simp [prefixMatch, he]

theorem suffixMatch_exact {α : Type*} [DecidableEq α] (as bs pre : List α) :
    suffixMatch (fun a b => decide (a = b)) as bs = (pre, true) ↔ as = pre ++ bs := by
  constructor
  · intro h
    have he : prefixMatch (fun a b => decide (a = b)) as.reverse bs.reverse = (pre.reverse, true) := by
      have hh := congrArg (fun p : List α × Bool => (p.1.reverse, p.2)) h
      simpa only [suffixMatch, List.reverse_reverse] using hh
    have hs := (prefixMatch_exact as.reverse bs.reverse pre.reverse).mp he
    simpa only [List.reverse_reverse, List.reverse_append] using congrArg List.reverse hs
  · intro h
    have he : as.reverse = bs.reverse ++ pre.reverse := by rw [h, List.reverse_append]
    have hm := (prefixMatch_exact as.reverse bs.reverse pre.reverse).mpr he
    simp only [suffixMatch, hm, List.reverse_reverse]

theorem prefixMatch_map {α β : Type*} [DecidableEq β] (equal : α → α → Bool) (value : α → β)
    (as bs : List α) (he : ∀ a ∈ as, ∀ b ∈ bs, equal a b = true ↔ value a = value b) :
    ((prefixMatch equal as bs).1.map value, (prefixMatch equal as bs).2) =
      prefixMatch (fun a b => decide (a = b)) (as.map value) (bs.map value) := by
  revert as he
  induction bs with
  | nil => intro as he; cases as <;> rfl
  | cons b bs ih =>
    intro as he
    cases as with
    | nil => rfl
    | cons a as =>
      have hh := he a List.mem_cons_self b List.mem_cons_self
      cases hc : equal a b with
      | true =>
        have hv := hh.mp hc
        simpa [prefixMatch, hc, hv] using
          ih as (fun x hx y hy => he x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
      | false =>
        have hv : value a ≠ value b := by
          intro hv
          have ht := hh.mpr hv
          simp only [hc, Bool.false_eq_true] at ht
        simp [prefixMatch, hc, hv]

theorem suffixMatch_map {α β : Type*} [DecidableEq β] (equal : α → α → Bool) (value : α → β)
    (as bs : List α) (he : ∀ a ∈ as, ∀ b ∈ bs, equal a b = true ↔ value a = value b) :
    ((suffixMatch equal as bs).1.map value, (suffixMatch equal as bs).2) =
      suffixMatch (fun a b => decide (a = b)) (as.map value) (bs.map value) := by
  have hm := prefixMatch_map equal value as.reverse bs.reverse
    (fun a ha b hb => he a (List.mem_reverse.mp ha) b (List.mem_reverse.mp hb))
  have hh := congrArg (fun p : List β × Bool => (p.1.reverse, p.2)) hm
  simpa only [suffixMatch, List.map_reverse] using hh

abbrev State (α : Type*) := List α × Bool

def matchStep {α : Type*} (equal : α → α → Bool) (b : α) (s : State α) : State α :=
  cond s.2 (match s.1 with
    | [] => ([], false)
    | a :: as => cond (equal a b) (as, true) (a :: as, false)) s

private theorem match_fold_failed {α : Type*} (equal : α → α → Bool) (as bs : List α) :
    bs.foldl (fun s b => matchStep equal b s) (as, false) = (as, false) := by
  induction bs <;> simp_all [matchStep]

theorem prefixMatch_fold {α : Type*} (equal : α → α → Bool) (as bs : List α) :
    bs.foldl (fun s b => matchStep equal b s) (as, true) = prefixMatch equal as bs := by
  induction bs generalizing as with
  | nil => cases as <;> rfl
  | cons b bs ih =>
    cases as with
    | nil =>
      change bs.foldl (fun s b => matchStep equal b s) ([], false) = ([], false)
      exact match_fold_failed equal [] bs
    | cons a as =>
      cases he : equal a b with
      | false =>
        have hs : matchStep equal b (a :: as, true) = (a :: as, false) := by
          simp only [matchStep, he, Bool.cond_true, Bool.cond_false]
        have hp : prefixMatch equal (a :: as) (b :: bs) = (a :: as, false) := by
          simp only [prefixMatch, he, Bool.cond_false]
        rw [List.foldl_cons, hs, hp]
        exact match_fold_failed equal (a :: as) bs
      | true =>
        have hs : matchStep equal b (a :: as, true) = (as, true) := by
          simp only [matchStep, he, Bool.cond_true]
        have hp : prefixMatch equal (a :: as) (b :: bs) = prefixMatch equal as bs := by
          simp only [prefixMatch, he, Bool.cond_true]
        rw [List.foldl_cons, hs, hp]
        exact ih as

private def matchNumeric {α : Type*} (default : α) (equal : α → α → Bool)
    (b : α) (s : State α) : State α :=
  cond s.2 (cond (s.1.length == 0) ([], false)
    (cond (equal (s.1[0]?.getD default) b) (s.1.tail, true) (s.1, false))) s

private theorem matchNumeric_eq {α : Type*} (default : α) (equal : α → α → Bool)
    (b : α) (s : State α) : matchNumeric default equal b s = matchStep equal b s := by
  rcases s with ⟨as, ok⟩
  cases ok <;> cases as <;> simp [matchNumeric, matchStep]

theorem prefixMatch_primrec {α Data : Type*} [Primcodable α] [Primcodable Data]
    (default : α) (equal : Data → α → α → Bool)
    (he : Primrec (fun p : Data × (α × α) => equal p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Data × (List α × List α) => prefixMatch (equal p.1) p.2.1 p.2.2) := by
  have hs : Primrec₂ (fun p : Data × (List α × List α) => fun z : State α × α =>
      matchNumeric default (equal p.1) z.2 z.1) := by
    let Input := (Data × (List α × List α)) × (State α × α)
    have hp : Primrec (fun p : Input => p.2.1) := Primrec.fst.comp Primrec.snd
    have has : Primrec (fun p : Input => p.2.1.1) := Primrec.fst.comp hp
    have hok : Primrec (fun p : Input => p.2.1.2) := Primrec.snd.comp hp
    have hb : Primrec (fun p : Input => p.2.2) := Primrec.snd.comp Primrec.snd
    have hhead : Primrec (fun p : Input => p.2.1.1[0]?.getD default) :=
      Primrec.option_getD.comp (Primrec.list_getElem?.comp has (Primrec.const 0)) (Primrec.const default)
    have hcmp : Primrec (fun p : Input => equal p.1.1 (p.2.1.1[0]?.getD default) p.2.2) :=
      he.comp ((Primrec.fst.comp Primrec.fst).pair (hhead.pair hb))
    exact (hok.cond ((Primrec.beq.comp (Primrec.list_length.comp has) (Primrec.const 0)).cond
      (Primrec.const ([], false)) (hcmp.cond ((Primrec.list_tail.comp has).pair (Primrec.const true))
        (has.pair (Primrec.const false)))) hp).to₂
  have hf : Primrec (fun p : Data × (List α × List α) =>
      p.2.2.foldl (fun z b => matchNumeric default (equal p.1) b z) (p.2.1, true)) :=
    Primrec.list_foldl (Primrec.snd.comp Primrec.snd)
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.const true)) hs
  have hh : (fun p : Data × (List α × List α) =>
      p.2.2.foldl (fun z b => matchNumeric default (equal p.1) b z) (p.2.1, true)) =
      (fun p : Data × (List α × List α) => prefixMatch (equal p.1) p.2.1 p.2.2) := by
    funext p
    simp only [matchNumeric_eq]
    exact prefixMatch_fold _ _ _
  rw [hh] at hf
  exact hf

theorem suffixMatch_primrec {α Data : Type*} [Primcodable α] [Primcodable Data]
    (default : α) (equal : Data → α → α → Bool)
    (he : Primrec (fun p : Data × (α × α) => equal p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Data × (List α × List α) => suffixMatch (equal p.1) p.2.1 p.2.2) := by
  have hp : Primrec (fun p : Data × (List α × List α) =>
      prefixMatch (equal p.1) p.2.1.reverse p.2.2.reverse) :=
    (prefixMatch_primrec default equal he).comp (Primrec.fst.pair
    ((Primrec.list_reverse.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.list_reverse.comp (Primrec.snd.comp Primrec.snd))))
  exact (Primrec.list_reverse.comp (Primrec.fst.comp hp)).pair (Primrec.snd.comp hp)

theorem anf_prefix {xs ys : List Ordinal.{u}} (hn : IsAdditiveNormalForm (xs ++ ys)) : IsAdditiveNormalForm xs :=
  ⟨fun a ha => hn.1 a (List.mem_append.mpr (Or.inl ha)), (List.pairwise_append.mp hn.2).1⟩

theorem normalizePrincipal_eq_of_normal (xs : List Ordinal.{u}) (hn : IsAdditiveNormalForm xs) :
    normalizePrincipal xs = xs :=
  additiveNormalForm_unique (normalizePrincipal_normal xs hn.1) hn (principalSum_normalizePrincipal xs hn.1)

/-- Actual absorption retains the whole normal right word, while the
surviving left prefix has sum at most the original left sum. -/
theorem normalize_suffix_le (xs ys : List Ordinal.{u}) (hy : IsAdditiveNormalForm ys) :
    ∃ pre, normalizePrincipal (xs ++ ys) = pre ++ ys ∧ principalSum pre ≤ principalSum xs := by
  classical
  induction xs with
  | nil => exact ⟨[], by simpa using normalizePrincipal_eq_of_normal ys hy, le_rfl⟩
  | cons a xs ih =>
    obtain ⟨pre, hp, hv⟩ := ih
    cases ht : pre ++ ys with
    | nil =>
      have hz := List.append_eq_nil_iff.mp ht
      refine ⟨[a], ?_, ?_⟩
      · change prependPrincipal a (normalizePrincipal (xs ++ ys)) = [a] ++ ys
        rw [hp, ht, hz.2]
        rfl
      · simpa only [principalSum, add_zero] using (le_self_add : a ≤ a + principalSum xs)
    | cons b bs =>
      by_cases hab : a < b
      · refine ⟨pre, ?_, hv.trans le_add_self⟩
        simp only [List.cons_append, normalizePrincipal, hp, ht, prependPrincipal, if_pos hab]
      · refine ⟨a :: pre, ?_, add_le_add_right hv a⟩
        simp only [List.cons_append, normalizePrincipal, hp, ht, prependPrincipal, if_neg hab]

/-- Every ordinal solution yields a genuine ANF suffix and a prefix <=g.
There is no project-code or admitted-notation restriction on g. -/
theorem solution_suffix (a b g : Ordinal.{u}) (he : a = g + b) :
    ∃ pre, canonicalANF a = pre ++ canonicalANF b ∧ principalSum pre ≤ g := by
  obtain ⟨pre, hp, hv⟩ := normalize_suffix_le (canonicalANF g) (canonicalANF b) (canonicalANF_normal b)
  refine ⟨pre, ?_, hv.trans_eq (principalSum_canonicalANF g)⟩
  rw [he, canonicalANF_add]
  exact hp

def SourceSpec (a b z : Ordinal.{u}) : Prop := if a ≤ b then z = 0 else
  ((a = z + b ∧ ∀ g : Ordinal.{u}, a = g + b → z ≤ g) ∨
    ((∀ g : Ordinal.{u}, a ≠ g + b) ∧ z = a))

noncomputable def rightSubtract (a b : Ordinal.{u}) : Ordinal.{u} := by
  classical
  exact if a ≤ b then 0 else
    let p := suffixMatch (fun x y => decide (x = y)) (canonicalANF a) (canonicalANF b)
    cond p.2 (principalSum p.1) a

theorem rightSubtract_spec (a b : Ordinal.{u}) : SourceSpec a b (rightSubtract a b) := by
  classical
  by_cases hab : a ≤ b
  · simp only [SourceSpec, rightSubtract, if_pos hab]
  · simp only [rightSubtract, if_neg hab]
    let p := suffixMatch (fun x y => decide (x = y)) (canonicalANF a) (canonicalANF b)
    change SourceSpec a b (cond p.2 (principalSum p.1) a)
    cases hp : p.2 with
    | true =>
      have ht : suffixMatch (fun x y => decide (x = y)) (canonicalANF a) (canonicalANF b) = (p.1, true) :=
        by change p = (p.1, true); exact Prod.ext rfl hp
      have he := (suffixMatch_exact _ _ _).mp ht
      have hv : a = principalSum p.1 + b := by
        have hh := congrArg principalSum he
        simpa only [principalSum_append, principalSum_canonicalANF] using hh
      have hmin : ∀ g : Ordinal.{u}, a = g + b → principalSum p.1 ≤ g := by
        intro g hg
        obtain ⟨pre, hpre, hb⟩ := solution_suffix a b g hg
        have hsame : p.1 = pre := List.append_cancel_right (he.symm.trans hpre)
        simpa only [hsame] using hb
      simp only [SourceSpec, if_neg hab, hp, Bool.cond_true]
      exact Or.inl ⟨hv, hmin⟩
    | false =>
      have hn : ∀ g : Ordinal.{u}, a ≠ g + b := by
        intro g hg
        obtain ⟨pre, hpre, _⟩ := solution_suffix a b g hg
        have ht := (suffixMatch_exact _ _ pre).mpr hpre
        have hb := congrArg Prod.snd ht
        change p.2 = true at hb
        simp only [hp, Bool.false_eq_true] at hb
      simp only [SourceSpec, if_neg hab, hp, Bool.cond_false]
      exact Or.inr ⟨hn, trivial⟩

theorem sourceSpec_unique (a b z v : Ordinal.{u}) (hz : SourceSpec a b z) (hv : SourceSpec a b v) : z = v := by
  by_cases hab : a ≤ b
  · exact (by simpa only [SourceSpec, if_pos hab] using hz : z = 0).trans
      (by simpa only [SourceSpec, if_pos hab] using hv : v = 0).symm
  · have hzs := (by simpa only [SourceSpec, if_neg hab] using hz :
        (a = z + b ∧ ∀ g, a = g + b → z ≤ g) ∨ ((∀ g, a ≠ g + b) ∧ z = a))
    have hvs := (by simpa only [SourceSpec, if_neg hab] using hv :
        (a = v + b ∧ ∀ g, a = g + b → v ≤ g) ∨ ((∀ g, a ≠ g + b) ∧ v = a))
    rcases hzs with ⟨hz, hmz⟩ | ⟨hnz, hz⟩ <;> rcases hvs with ⟨hv, hmv⟩ | ⟨hnv, hv⟩
    · exact le_antisymm (hmz v hv) (hmv z hz)
    · exact False.elim (hnv z hz)
    · exact False.elim (hnz v hv)
    · exact hz.trans hv.symm

theorem rightSubtract_of_le (a b : Ordinal.{u}) (h : a ≤ b) : rightSubtract a b = 0 := by
  classical
  simp only [rightSubtract, if_pos h]

theorem rightSubtract_zero_right (a : Ordinal.{u}) : rightSubtract a 0 = a := by
  have hs := rightSubtract_spec a 0
  by_cases ha : a ≤ 0
  · rw [rightSubtract_of_le a 0 ha, le_zero_iff.mp ha]
  · have ht : (a = rightSubtract a 0 + 0 ∧ ∀ g, a = g + 0 → rightSubtract a 0 ≤ g) ∨
        ((∀ g, a ≠ g + 0) ∧ rightSubtract a 0 = a) := by simpa only [SourceSpec, if_neg ha] using hs
    rcases ht with ⟨he, _⟩ | ⟨hn, _⟩
    · simpa only [add_zero] using he.symm
    · exact False.elim (hn a (add_zero a).symm)

theorem rightSubtract_minimum (a b : Ordinal.{u}) (hab : b < a) (hex : ∃ g, a = g + b) :
    a = rightSubtract a b + b ∧ ∀ g : Ordinal.{u}, a = g + b → rightSubtract a b ≤ g := by
  have hs : (a = rightSubtract a b + b ∧ ∀ g, a = g + b → rightSubtract a b ≤ g) ∨
      ((∀ g, a ≠ g + b) ∧ rightSubtract a b = a) := by
    simpa only [SourceSpec, if_neg (not_le_of_gt hab)] using rightSubtract_spec a b
  rcases hs with hs | ⟨hn, _⟩
  · exact hs
  · obtain ⟨g, hg⟩ := hex
    exact False.elim (hn g hg)

theorem rightSubtract_no_solution (a b : Ordinal.{u}) (hab : b < a) (hn : ∀ g, a ≠ g + b) :
    rightSubtract a b = a := by
  have hs : (a = rightSubtract a b + b ∧ ∀ g, a = g + b → rightSubtract a b ≤ g) ∨
      ((∀ g, a ≠ g + b) ∧ rightSubtract a b = a) := by
    simpa only [SourceSpec, if_neg (not_le_of_gt hab)] using rightSubtract_spec a b
  rcases hs with ⟨he, _⟩ | ⟨_, he⟩
  · exact False.elim (hn _ he)
  · exact he

theorem rightSubtract_le (a b : Ordinal.{u}) : rightSubtract a b ≤ a := by
  have hs := rightSubtract_spec a b
  by_cases hab : a ≤ b
  · rw [rightSubtract_of_le a b hab]
    exact zero_le
  · have ht : (a = rightSubtract a b + b ∧ ∀ g, a = g + b → rightSubtract a b ≤ g) ∨
        ((∀ g, a ≠ g + b) ∧ rightSubtract a b = a) := by simpa only [SourceSpec, if_neg hab] using hs
    rcases ht with ⟨he, _⟩ | ⟨_, he⟩
    · exact le_self_add.trans_eq he.symm
    · exact he.le

end Alexander313.Wilken.OrdinalRightSubtraction
