import Alexander313.Wilken.SourceOneNormalComparison
import Alexander313.Effective.RecordedGuardPrograms

/-! # Literal lists used by the executing comparison

Lexicographic comparison is implemented by a finite left fold with an
explicit decided flag. The actual outer theta atoms are computed by a
literal value fold. Numeric constituent bounds concern syntax codes only.
There is no semantic order or computability input. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.SourceOne.Comparison.Effective

abbrev LexState (α : Type) := List α × (Bool × Bool)

def lexStep {α : Type} (cmp : α → α → Bool) (a : α) (s : LexState α) : LexState α :=
  if s.2.1 then s else
    match s.1 with
    | [] => ([], true, false)
    | b :: bs => (bs, cmp a b || cmp b a, cmp a b)

def lexFinish {α : Type} (s : LexState α) : Bool :=
  cond s.2.1 s.2.2 (decide (0 < s.1.length))

def lexRun {α : Type} (cmp : α → α → Bool) (as bs : List α) : Bool :=
  lexFinish (as.foldl (fun s a => lexStep cmp a s) (bs, false, false))

private def lexNumeric {α : Type} (default : α) (cmp : α → α → Bool)
    (a : α) (s : LexState α) : LexState α :=
  let b := s.1[0]?.getD default
  cond s.2.1 s (cond (s.1.length == 0) ([], true, false)
    (s.1.tail, cmp a b || cmp b a, cmp a b))

private theorem lexNumeric_eq {α : Type} (default : α) (cmp : α → α → Bool)
    (a : α) (s : LexState α) : lexNumeric default cmp a s = lexStep cmp a s := by
  rcases s with ⟨bs, flag, result⟩
  cases flag <;> cases bs <;> rfl

private theorem lex_absorbed {α : Type} (cmp : α → α → Bool)
    (as bs : List α) (result : Bool) :
    as.foldl (fun s a => lexStep cmp a s) (bs, true, result) = (bs, true, result) := by
  induction as <;> simp_all [lexStep]

theorem lexRun_eq {α : Type} (cmp : α → α → Bool) (as bs : List α) :
    lexRun cmp as bs = lexLT cmp as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [lexRun, lexFinish, lexLT]
  | cons a as ih =>
    cases bs with
    | nil =>
      change lexFinish (as.foldl (fun s a => lexStep cmp a s) ([], true, false)) = false
      rw [lex_absorbed]
      rfl
    | cons b bs =>
      change lexFinish (as.foldl (fun s a => lexStep cmp a s)
        (bs, cmp a b || cmp b a, cmp a b)) =
        (cmp a b || (!cmp b a && lexLT cmp as bs))
      cases hab : cmp a b <;> cases hba : cmp b a <;>
        simp only [Bool.false_or, Bool.true_or, Bool.not_false, Bool.not_true,
          Bool.true_and, Bool.false_and]
      · exact ih bs
      · rw [lex_absorbed]; rfl
      · rw [lex_absorbed]; rfl
      · rw [lex_absorbed]; rfl

theorem lexLT_primrec {α Data : Type} [Primcodable α] [Primcodable Data]
    (default : α) (cmp : Data → α → α → Bool)
    (hc : Primrec (fun p : Data × (α × α) => cmp p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Data × (List α × List α) => lexLT (cmp p.1) p.2.1 p.2.2) := by
  have hs : Primrec₂ (fun p : Data × (List α × List α) =>
      fun q : LexState α × α => lexNumeric default (cmp p.1) q.2 q.1) := by
    have hd : Primrec (fun p : (Data × (List α × List α)) × (LexState α × α) => p.1.1) :=
      Primrec.fst.comp Primrec.fst
    have ha : Primrec (fun p : (Data × (List α × List α)) × (LexState α × α) => p.2.2) :=
      Primrec.snd.comp Primrec.snd
    have hstate : Primrec (fun p : (Data × (List α × List α)) × (LexState α × α) => p.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hbs := Primrec.fst.comp hstate
    have hflag := Primrec.fst.comp (Primrec.snd.comp hstate)
    have hhead := Primrec.option_getD.comp
      (Primrec.list_getElem?.comp hbs (Primrec.const 0)) (Primrec.const default)
    have hab := hc.comp (hd.pair (ha.pair hhead))
    have hba := hc.comp (hd.pair (hhead.pair ha))
    have hn := Primrec.beq.comp (Primrec.list_length.comp hbs) (Primrec.const 0)
    exact (hflag.cond hstate (hn.cond (Primrec.const ([], true, false))
      ((Primrec.list_tail.comp hbs).pair ((Primrec.or.comp hab hba).pair hab)))).to₂
  have hlist : Primrec (fun p : Data × (List α × List α) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hstart : Primrec (fun p : Data × (List α × List α) => (p.2.2, false, false)) :=
    (Primrec.snd.comp Primrec.snd).pair (Primrec.const (false, false))
  have hstepEq : (fun p : (Data × (List α × List α)) × (LexState α × α) =>
      lexNumeric default (cmp p.1.1) p.2.2 p.2.1) =
      (fun p : (Data × (List α × List α)) × (LexState α × α) =>
        lexStep (cmp p.1.1) p.2.2 p.2.1) := by
    funext p
    exact lexNumeric_eq _ _ _ _
  change Primrec (fun p : (Data × (List α × List α)) × (LexState α × α) =>
    lexNumeric default (cmp p.1.1) p.2.2 p.2.1) at hs
  rw [hstepEq] at hs
  have hfold := Primrec.list_foldl hlist hstart hs.to₂
  have hflag := Primrec.fst.comp (Primrec.snd.comp hfold)
  have hresult := Primrec.snd.comp (Primrec.snd.comp hfold)
  have hremaining := (Primrec.nat_lt.comp (Primrec.const 0)
    (Primrec.list_length.comp (Primrec.fst.comp hfold))).decide
  have hrun := hflag.cond hresult hremaining
  have heq : (fun p : Data × (List α × List α) => lexRun (cmp p.1) p.2.1 p.2.2) =
      (fun p : Data × (List α × List α) => lexLT (cmp p.1) p.2.1 p.2.2) := by
    funext p
    exact lexRun_eq _ _ _
  change Primrec (fun p : Data × (List α × List α) => lexRun (cmp p.1) p.2.1 p.2.2) at hrun
  rw [heq] at hrun
  exact hrun

theorem listAll_primrec {α Data : Type} [Primcodable α] [Primcodable Data]
    (test : Data → α → Bool) (ht : Primrec₂ test) :
    Primrec₂ (fun d (xs : List α) => xs.all (test d)) := by
  have h := RecordedGuardProgram.allCheck_primrec test ht
  have heq : (fun p : Data × List α => RecordedGuardProgram.allCheck (test p.1) p.2) =
      (fun p : Data × List α => p.2.all (test p.1)) := by
    funext p
    induction p.2 <;> simp_all [RecordedGuardProgram.allCheck]
  change Primrec (fun p : Data × List α => RecordedGuardProgram.allCheck (test p.1) p.2) at h
  rw [heq] at h
  exact h.to₂

theorem listAny_primrec {α Data : Type} [Primcodable α] [Primcodable Data]
    (test : Data → α → Bool) (ht : Primrec₂ test) :
    Primrec₂ (fun d (xs : List α) => xs.any (test d)) := by
  have h := RecordedGuardProgram.anyCheck_primrec test ht
  have heq : (fun p : Data × List α => RecordedGuardProgram.anyCheck (test p.1) p.2) =
      (fun p : Data × List α => p.2.any (test p.1)) := by
    funext p
    induction p.2 <;> simp_all [RecordedGuardProgram.anyCheck]
  change Primrec (fun p : Data × List α => RecordedGuardProgram.anyCheck (test p.1) p.2) at h
  rw [heq] at h
  exact h.to₂

private def atomParameter (_ : Unit) (p : Nat) : RelativeTerm Nat × List (RelativeTerm Nat) :=
  (.parameter p, [])

private def atomSum (a b : RelativeTerm Nat × List (RelativeTerm Nat)) :
    RelativeTerm Nat × List (RelativeTerm Nat) := (.sum a.1 b.1, a.2 ++ b.2)

private def atomTheta (_ : Unit) (k : Nat) (a : RelativeTerm Nat × List (RelativeTerm Nat)) :
    RelativeTerm Nat × List (RelativeTerm Nat) := (.theta k a.1, [.theta k a.1])

theorem thetaAtoms_primrec : Primrec (thetaAtoms (Parameter := Nat)) := by
  have hp : Primrec₂ atomParameter :=
    ((parameter_primrec.comp Primrec.snd).pair (Primrec.const [])).to₂
  have hs : Primrec₂ atomSum :=
    ((sum_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂
  have ht : Primrec (fun p : Unit × (Nat × (RelativeTerm Nat × List (RelativeTerm Nat))) =>
      atomTheta p.1 p.2.1 p.2.2) := by
    have hterm : Primrec (fun p : Unit × (Nat × (RelativeTerm Nat × List (RelativeTerm Nat))) =>
        RelativeTerm.theta p.2.1 p.2.2.1) := theta_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    exact hterm.pair (Primrec.list_cons.comp hterm (Primrec.const []))
  let fold := ValueFold.term atomParameter atomSum atomTheta ()
  have hf : Primrec fold := (ValueFold.term_primrec atomParameter atomSum atomTheta
    (.parameter 0, []) hp hs ht).comp (Primrec.const ()) Primrec.id
  have heq : ∀ t : RelativeTerm Nat, fold t = (t, thetaAtoms t) := by
    intro t
    induction t <;> simp_all [fold, ValueFold.term, atomParameter, atomSum, atomTheta, thetaAtoms]
  have h := Primrec.snd.comp hf
  have hfun : (fun t => (fold t).2) = thetaAtoms := by
    funext t
    rw [heq]
  rw [hfun] at h
  exact h

private theorem pair_left_le (a b : Nat) : a ≤ Nat.pair a b := by
  simpa only [Nat.unpair_pair] using Nat.unpair_left_le (Nat.pair a b)

private theorem pair_right_le (a b : Nat) : b ≤ Nat.pair a b := by
  simpa only [Nat.unpair_pair] using Nat.unpair_right_le (Nat.pair a b)

theorem sum_left_code_lt (a b : RelativeTerm Nat) : a.code < (RelativeTerm.sum a b).code :=
  (pair_left_le a.code b.code).trans_lt (Nat.lt_succ_of_le (pair_right_le 1 _))

theorem sum_right_code_lt (a b : RelativeTerm Nat) : b.code < (RelativeTerm.sum a b).code :=
  (pair_right_le a.code b.code).trans_lt (Nat.lt_succ_of_le (pair_right_le 1 _))

theorem theta_argument_code_lt (k : Nat) (a : RelativeTerm Nat) : a.code < (RelativeTerm.theta k a).code :=
  (pair_right_le k a.code).trans_lt (Nat.lt_succ_of_le (pair_right_le 2 _))

theorem thetaAtoms_code_le (t a : RelativeTerm Nat) (ha : a ∈ thetaAtoms t) : a.code ≤ t.code := by
  induction t with
  | parameter p => simp [thetaAtoms] at ha
  | sum x y ihx ihy =>
    rcases List.mem_append.mp ha with hx | hy
    · exact (ihx hx).trans (sum_left_code_lt x y).le
    · exact (ihy hy).trans (sum_right_code_lt x y).le
  | theta k x => have he : a = .theta k x := List.mem_singleton.mp ha; subst a; exact le_rfl

theorem exposedThetaList_code_le (m : Nat) (t a : RelativeTerm Nat)
    (ha : a ∈ exposedThetaList m t) : a.code ≤ t.code := by
  induction t with
  | parameter p => simp [exposedThetaList] at ha
  | sum x y ihx ihy =>
    rcases List.mem_append.mp ha with hx | hy
    · exact (ihx hx).trans (sum_left_code_lt x y).le
    · exact (ihy hy).trans (sum_right_code_lt x y).le
  | theta k x ih =>
    by_cases hkm : k = m
    · have he : a = .theta k x := by simpa [exposedThetaList, hkm] using ha
      subst a
      exact le_rfl
    · by_cases hmk : m < k
      · have hx : a ∈ exposedThetaList m x := by simpa [exposedThetaList, hkm, hmk] using ha
        exact (ih hx).trans (theta_argument_code_lt k x).le
      · simp [exposedThetaList, hkm, hmk] at ha

theorem all_congr_on {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ x ∈ xs, f x = g x) : xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, h x (List.mem_cons_self)]
    rw [ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem any_congr_on {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ x ∈ xs, f x = g x) : xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons, h x (List.mem_cons_self)]
    rw [ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem lex_congr_on {α : Type} (as bs : List α) (f g : α → α → Bool)
    (h : ∀ a ∈ as, ∀ b ∈ bs, f a b = g a b ∧ f b a = g b a) :
    lexLT f as bs = lexLT g as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      have hh := h a (List.mem_cons_self) b (List.mem_cons_self)
      simp only [lexLT, hh.1, hh.2]
      rw [ih bs (fun x hx y hy => h x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem b hy))]

end Alexander313.Wilken.RelativeTerm.SourceOne.Comparison.Effective
