import Alexander313.Effective.HereditaryThetaPrograms

/-!
# Least numerical normal representatives of actual hereditary values

Every old accepted union code has a displayed accepted normal representative:
its genuine normalized tree at the original level. A bounded primitive
recursion searches through that representative's literal numerical code.
Exact old equality and normal admission make the result the least accepted
normal union code of the original value, independently of the search bound.

These are numerical least-code representatives. They do not identify Wilken's
printed structural canonical forms, independent enumeration indices, endpoint
tags, tracking or edge relations. Original admission and interpretation remain
unchanged. All proof terms are uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Canonical

open Theta

def acceptedUnion (q : Nat) : Bool := acceptedLowCode q.unpair.1 q.unpair.2

theorem acceptedUnion_iff (q : Nat) : acceptedUnion q = true ↔
    unionCheck q = true ∧ Normal q.unpair.1 (ThetaCourse.rawTree q.unpair.2) := by
  exact acceptedLowCode_iff q.unpair.1 q.unpair.2

theorem acceptedUnion_original {q : Nat} (hq : acceptedUnion q = true) :
    unionCheck q = true := ((acceptedUnion_iff q).mp hq).1

def eligible (q c : Nat) : Bool :=
  acceptedUnion c && HereditaryThetaProgram.crossEqual
    q.unpair.1 q.unpair.2 c.unpair.1 c.unpair.2

theorem eligible_exact (q c : Nat) : eligible q c = true ↔
    unionCheck q = true ∧ acceptedUnion c = true ∧
      unionInterpretation q = unionInterpretation c := by
  rw [eligible, Bool.and_eq_true, HereditaryThetaProgram.crossEqual_exact]
  constructor
  · rintro ⟨hc, hq, hcold, he⟩
    exact ⟨hq, hc, he⟩
  · rintro ⟨hq, hc, he⟩
    exact ⟨hc, hq, acceptedUnion_original hc, he⟩

def witness (q : Nat) : Nat :=
  Nat.pair q.unpair.1 (Normalization.normalizeCode q.unpair.1 q.unpair.2)

theorem witness_eligible (q : Nat) (hq : unionCheck q = true) : eligible q (witness q) = true := by
  have hn := Normalization.normalizeCode_acceptedLow q.unpair.1 q.unpair.2 hq
  apply (eligible_exact q (witness q)).mpr
  refine ⟨hq, ?_, ?_⟩
  · simpa only [witness, acceptedUnion, Nat.unpair_pair] using hn.1
  · simpa only [witness, unionInterpretation, Nat.unpair_pair] using hn.2.symm

/-- The scan retains the first successful index. If none has succeeded, its
result is the current bound. The actual normal witness licenses that endpoint. -/
def search (q : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cond (eligible q (search q n)) (search q n) (n + 1)

theorem search_spec (q n : Nat) :
    search q n ≤ n ∧ (∀ c < search q n, eligible q c = false) ∧
      (eligible q (search q n) = false → search q n = n) := by
  induction n with
  | zero => exact ⟨le_rfl, fun c hc => False.elim (Nat.not_lt_zero c hc), fun _ => rfl⟩
  | succ n ih =>
    cases he : eligible q (search q n) with
    | true =>
      have hstep : search q (n + 1) = search q n := by
        simp only [search, he, Bool.cond_true]
      rw [hstep]
      refine ⟨ih.1.trans (Nat.le_succ n), ih.2.1, ?_⟩
      intro hfalse
      rw [he] at hfalse
      cases hfalse
    | false =>
      have hstep : search q (n + 1) = n + 1 := by
        simp only [search, he, Bool.cond_false]
      rw [hstep]
      refine ⟨le_rfl, ?_, fun _ => rfl⟩
      intro c hc
      have hlast : search q n = n := ih.2.2 he
      by_cases hcn : c < n
      · exact ih.2.1 c (by simpa only [hlast] using hcn)
      · have hce : c = n := by omega
        simpa only [hce, hlast] using he

theorem search_eligible (q n : Nat) (hn : eligible q n = true) :
    eligible q (search q n) = true := by
  have hs := search_spec q n
  cases he : eligible q (search q n) with
  | true => rfl
  | false =>
    have hlast := hs.2.2 he
    rw [hlast, hn] at he
    cases he

theorem search_minimal (q n c : Nat) (hc : eligible q c = true) : search q n ≤ c := by
  by_contra h
  have hsmall : c < search q n := lt_of_not_ge h
  have hfalse := (search_spec q n).2.1 c hsmall
  rw [hc] at hfalse
  cases hfalse

def canonicalize (q : Nat) : Nat := cond (unionCheck q) (search q (witness q)) 0

theorem canonicalize_rejected (q : Nat) (hq : unionCheck q = false) : canonicalize q = 0 := by
  simp only [canonicalize, hq, Bool.cond_false]

theorem canonicalize_spec (q : Nat) (hq : unionCheck q = true) :
    acceptedUnion (canonicalize q) = true ∧
      unionInterpretation (canonicalize q) = unionInterpretation q ∧
      ∀ c, acceptedUnion c = true → unionInterpretation c = unionInterpretation q →
        canonicalize q ≤ c := by
  have hw := witness_eligible q hq
  have hs := (eligible_exact q (search q (witness q))).mp (search_eligible q _ hw)
  simp only [canonicalize, hq, Bool.cond_true]
  refine ⟨hs.2.1, hs.2.2.symm, ?_⟩
  intro c hc he
  exact search_minimal q (witness q) c ((eligible_exact q c).mpr ⟨hq, hc, he.symm⟩)

theorem canonicalize_original (q : Nat) (hq : unionCheck q = true) :
    unionCheck (canonicalize q) = true := acceptedUnion_original (canonicalize_spec q hq).1

theorem canonicalize_normal (q : Nat) (hq : unionCheck q = true) :
    Normal (canonicalize q).unpair.1 (ThetaCourse.rawTree (canonicalize q).unpair.2) :=
  ((acceptedUnion_iff _).mp (canonicalize_spec q hq).1).2

theorem canonicalize_value (q : Nat) (hq : unionCheck q = true) :
    unionInterpretation (canonicalize q) = unionInterpretation q := (canonicalize_spec q hq).2.1

theorem canonicalize_bound (q : Nat) (hq : unionCheck q = true) : canonicalize q ≤ witness q := by
  simpa only [canonicalize, hq, Bool.cond_true] using (search_spec q (witness q)).1

theorem canonicalize_invariant (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true)
    (he : unionInterpretation q = unionInterpretation v) : canonicalize q = canonicalize v := by
  have hs := canonicalize_spec q hq
  have ht := canonicalize_spec v hv
  exact le_antisymm (hs.2.2 _ ht.1 (ht.2.1.trans he.symm))
    (ht.2.2 _ hs.1 (hs.2.1.trans he))

theorem canonicalize_eq_iff (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    canonicalize q = canonicalize v ↔ unionInterpretation q = unionInterpretation v := by
  constructor
  · intro he
    rw [← canonicalize_value q hq, ← canonicalize_value v hv, he]
  · exact canonicalize_invariant q v hq hv

theorem canonicalize_idempotent (q : Nat) (hq : unionCheck q = true) :
    canonicalize (canonicalize q) = canonicalize q :=
  (canonicalize_invariant q (canonicalize q) hq (canonicalize_original q hq)
    (canonicalize_value q hq).symm).symm

def check (q : Nat) : Bool := acceptedUnion q && (canonicalize q == q)

theorem check_exact (q : Nat) : check q = true ↔ acceptedUnion q = true ∧
    ∀ c, acceptedUnion c = true → unionInterpretation c = unionInterpretation q → q ≤ c := by
  simp only [check, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hq, he⟩
    refine ⟨hq, ?_⟩
    intro c hc hv
    have hmin := (canonicalize_spec q (acceptedUnion_original hq)).2.2 c hc hv
    simpa only [he] using hmin
  · rintro ⟨hq, hmin⟩
    have hs := canonicalize_spec q (acceptedUnion_original hq)
    exact ⟨hq, le_antisymm (hs.2.2 q hq rfl) (hmin _ hs.1 hs.2.1)⟩

theorem check_original {q : Nat} (hq : check q = true) : unionCheck q = true :=
  acceptedUnion_original ((check_exact q).mp hq).1

theorem check_normal {q : Nat} (hq : check q = true) :
    Normal q.unpair.1 (ThetaCourse.rawTree q.unpair.2) :=
  ((acceptedUnion_iff q).mp ((check_exact q).mp hq).1).2

theorem canonicalize_check (q : Nat) (hq : unionCheck q = true) : check (canonicalize q) = true := by
  simp only [check, (canonicalize_spec q hq).1, canonicalize_idempotent q hq,
    beq_self_eq_true, Bool.true_and]

theorem check_fixed {q : Nat} (hq : check q = true) : canonicalize q = q := by
  have he : (canonicalize q == q) = true := (Bool.and_eq_true_iff.mp hq).2
  exact beq_iff_eq.mp he

theorem check_value_injective (q v : Nat) (hq : check q = true) (hv : check v = true)
    (he : unionInterpretation q = unionInterpretation v) : q = v := by
  have h := canonicalize_invariant q v (check_original hq) (check_original hv) he
  simpa only [check_fixed hq, check_fixed hv] using h

theorem canonicalize_crossEqual (q v : Nat)
    (he : HereditaryThetaProgram.crossEqual q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2 = true) :
    canonicalize q = canonicalize v := by
  have hs := (HereditaryThetaProgram.crossEqual_exact _ _ _ _).mp he
  exact canonicalize_invariant q v hs.1 hs.2.1 hs.2.2

theorem lt_finiteBaseLimit_iff_code (ξ : Ordinal.{0}) : ξ < finiteBaseLimit ↔
    ∃ q : Nat, check q = true ∧ unionInterpretation q = ξ := by
  constructor
  · intro hξ
    obtain ⟨q, hq, he⟩ := (Hereditary.lt_finiteBaseLimit_iff_code ξ).mp hξ
    exact ⟨canonicalize q, canonicalize_check q hq, (canonicalize_value q hq).trans he⟩
  · rintro ⟨q, hq, he⟩
    exact (Hereditary.lt_finiteBaseLimit_iff_code ξ).mpr ⟨q, check_original hq, he⟩

theorem lt_finiteBaseLimit_iff_unique_code (ξ : Ordinal.{0}) : ξ < finiteBaseLimit ↔
    ∃! q : Nat, check q = true ∧ unionInterpretation q = ξ := by
  constructor
  · intro hξ
    obtain ⟨q, hq, he⟩ := (lt_finiteBaseLimit_iff_code ξ).mp hξ
    refine ⟨q, ⟨hq, he⟩, ?_⟩
    rintro v ⟨hv, hve⟩
    exact check_value_injective v q hv hq (hve.trans he.symm)
  · intro h
    obtain ⟨q, hq, huniq⟩ := h
    exact (lt_finiteBaseLimit_iff_code ξ).mpr ⟨q, hq⟩

def less (q v : Nat) : Bool :=
  (check q && check v) && HereditaryThetaProgram.crossLess
    q.unpair.1 q.unpair.2 v.unpair.1 v.unpair.2

theorem less_exact (q v : Nat) : less q v = true ↔
    check q = true ∧ check v = true ∧ unionInterpretation q < unionInterpretation v := by
  simp only [less, Bool.and_eq_true, and_assoc, HereditaryThetaProgram.crossLess_exact]
  constructor
  · rintro ⟨hq, hv, hqold, hvold, hlt⟩
    exact ⟨hq, hv, hlt⟩
  · rintro ⟨hq, hv, hlt⟩
    exact ⟨hq, hv, check_original hq, check_original hv, hlt⟩

def equal (q v : Nat) : Bool := (check q && check v) && (q == v)

theorem equal_exact (q v : Nat) : equal q v = true ↔
    check q = true ∧ check v = true ∧ unionInterpretation q = unionInterpretation v := by
  simp only [equal, Bool.and_eq_true, and_assoc, beq_iff_eq]
  constructor
  · rintro ⟨hq, hv, rfl⟩
    exact ⟨hq, hv, rfl⟩
  · rintro ⟨hq, hv, he⟩
    exact ⟨hq, hv, check_value_injective q v hq hv he⟩

def graph (q c : Nat) : Bool := (unionCheck q && check c) && (canonicalize q == c)

theorem graph_exact (q c : Nat) : graph q c = true ↔
    unionCheck q = true ∧ check c = true ∧ unionInterpretation q = unionInterpretation c := by
  simp only [graph, Bool.and_eq_true, and_assoc, beq_iff_eq]
  constructor
  · rintro ⟨hq, hc, he⟩
    refine ⟨hq, hc, ?_⟩
    rw [← canonicalize_value q hq, he]
  · rintro ⟨hq, hc, he⟩
    refine ⟨hq, hc, ?_⟩
    have h := canonicalize_invariant q c hq (check_original hc) he
    simpa only [check_fixed hc] using h

abbrev Code := {q : Nat // check q = true}

noncomputable def value (c : Code) : Ordinal.{0} := unionInterpretation c.1

theorem value_injective : Function.Injective value := by
  intro q v he
  apply Subtype.ext
  exact check_value_injective q.1 v.1 q.2 v.2 he

theorem value_lt_limit (q : Code) : value q < finiteBaseLimit :=
  (Hereditary.lt_finiteBaseLimit_iff_code _).mpr ⟨q.1, check_original q.2, rfl⟩

theorem value_covers {ξ : Ordinal.{0}} (hξ : ξ < finiteBaseLimit) : ∃ q : Code, value q = ξ := by
  obtain ⟨q, hq, hv⟩ := (lt_finiteBaseLimit_iff_code ξ).mp hξ
  exact ⟨⟨q, hq⟩, hv⟩

def orderLT : LT Code := ⟨fun q v => less q.1 v.1 = true⟩

theorem code_lt_iff (q v : Code) : @LT.lt Code orderLT q v ↔ value q < value v := by
  change less q.1 v.1 = true ↔ _
  simpa only [q.2, v.2, true_and, value] using less_exact q.1 v.1

theorem code_lt_trans {q v w : Code} (hqv : @LT.lt Code orderLT q v)
    (hvw : @LT.lt Code orderLT v w) : @LT.lt Code orderLT q w :=
  (code_lt_iff q w).mpr (((code_lt_iff q v).mp hqv).trans ((code_lt_iff v w).mp hvw))

theorem code_lt_irrefl (q : Code) : ¬@LT.lt Code orderLT q q := by
  rw [code_lt_iff]
  exact lt_irrefl _

theorem code_trichotomy (q v : Code) :
    @LT.lt Code orderLT q v ∨ q = v ∨ @LT.lt Code orderLT v q := by
  rcases lt_trichotomy (value q) (value v) with h | h | h
  · exact Or.inl ((code_lt_iff q v).mpr h)
  · exact Or.inr (Or.inl (value_injective h))
  · exact Or.inr (Or.inr ((code_lt_iff v q).mpr h))

noncomputable def intervalEquiv : Code ≃ Set.Iio finiteBaseLimit :=
  Equiv.ofBijective (fun q : Code => ⟨value q, value_lt_limit q⟩) (by
    constructor
    · intro q v he
      exact value_injective (congrArg Subtype.val he)
    · intro ξ
      obtain ⟨q, hq⟩ := value_covers ξ.2
      exact ⟨q, Subtype.ext hq⟩)

namespace Effective

theorem acceptedUnion_primrec : Primrec acceptedUnion :=
  Theta.Effective.acceptedLowCode_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)

theorem unionCheck_primrec : Primrec unionCheck :=
  Uniform.hereditaryLowCheckCode_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)

theorem eligible_primrec : Primrec₂ eligible := by
  have hq : Primrec (fun p : Nat × Nat => p.1.unpair) := Primrec.unpair.comp Primrec.fst
  have hc : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  exact (Primrec.and.comp (acceptedUnion_primrec.comp Primrec.snd)
    (HereditaryThetaProgram.crossEqual_primrec.comp (hq.pair hc))).to₂

theorem witness_primrec : Primrec witness :=
  Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
    (Normalization.Effective.normalizeCode_primrec.comp
      (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))

theorem search_primrec : Primrec₂ search := by
  have hs : Primrec₂ (fun q : Nat => fun p : Nat × Nat =>
      cond (eligible q p.2) p.2 (p.1 + 1)) :=
    ((eligible_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).cond
      (Primrec.snd.comp Primrec.snd) (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))).to₂
  have h := Primrec.nat_rec (Primrec.const 0) hs
  exact h.of_eq (by
    intro q n
    induction n <;> simp_all [search])

theorem canonicalize_primrec : Primrec canonicalize :=
  unionCheck_primrec.cond (search_primrec.comp Primrec.id witness_primrec) (Primrec.const 0)

theorem check_primrec : Primrec check :=
  Primrec.and.comp acceptedUnion_primrec (Primrec.beq.comp canonicalize_primrec Primrec.id)

theorem less_primrec : Primrec₂ less := by
  have hq : Primrec (fun p : Nat × Nat => p.1.unpair) := Primrec.unpair.comp Primrec.fst
  have hv : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  exact (Primrec.and.comp (Primrec.and.comp (check_primrec.comp Primrec.fst)
      (check_primrec.comp Primrec.snd))
    (HereditaryThetaProgram.crossLess_primrec.comp (hq.pair hv))).to₂

theorem equal_primrec : Primrec₂ equal :=
  (Primrec.and.comp (Primrec.and.comp (check_primrec.comp Primrec.fst)
      (check_primrec.comp Primrec.snd)) (Primrec.beq.comp Primrec.fst Primrec.snd)).to₂

theorem graph_primrec : Primrec₂ graph :=
  (Primrec.and.comp (Primrec.and.comp (unionCheck_primrec.comp Primrec.fst)
      (check_primrec.comp Primrec.snd))
    (Primrec.beq.comp (canonicalize_primrec.comp Primrec.fst) Primrec.snd)).to₂

theorem canonicalize_computable : Computable canonicalize := canonicalize_primrec.to_comp

theorem check_computable : Computable check := check_primrec.to_comp

end Effective
end Alexander313.Wilken.RelativeTerm.Hereditary.Canonical
