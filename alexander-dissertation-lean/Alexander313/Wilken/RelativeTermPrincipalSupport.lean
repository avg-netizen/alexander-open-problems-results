import Alexander313.Wilken.RelativeTermExposedCodes

/-!
# Full literal principal and parameter support

Definition 2.23 uses cutoff m, and continues inside a theta-m node. The
literal list below consequently includes nested theta-m nodes, whereas
the existing exposed list uses cutoff m+1 and stops at such a node.
The actual finite P^n_m is not identified with this full P_m. Their maxima
agree on normal admitted terms by the genuine argument-star inequality.
Atomic parameter support is literal; parameters are never expanded into
their canonical ANF. A written zero parameter is retained; identifying the
paper's parameter-free zero constant requires its separate syntax convention.
All proofs remain uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.PrincipalSupport

variable {Parameter : Type}

/-- Full-depth theta-m nodes outside the scope of a lower-index theta. -/
def principalList (m : Nat) : RelativeTerm Parameter → List (RelativeTerm Parameter)
  | .parameter _ => []
  | .sum a b => principalList m a ++ principalList m b
  | .theta k a => if m ≤ k then
      if k = m then .theta k a :: principalList m a else principalList m a
      else []

/-- Literal atomic parameters, including those inside every theta argument. -/
def parameterList : RelativeTerm Parameter → List Parameter
  | .parameter p => [p]
  | .sum a b => parameterList a ++ parameterList b
  | .theta _ a => parameterList a

@[simp] theorem principalList_theta_same (m : Nat) (a : RelativeTerm Parameter) :
    principalList m (.theta m a) = .theta m a :: principalList m a := by
  simp only [principalList, le_refl, if_true]

theorem principalList_theta_higher (m k : Nat) (a : RelativeTerm Parameter) (h : m < k) :
    principalList m (.theta k a) = principalList m a := by
  rw [principalList, if_pos h.le, if_neg (ne_of_gt h)]

theorem principalList_theta_lower (m k : Nat) (a : RelativeTerm Parameter) (h : k < m) :
    principalList m (.theta k a) = [] := by
  rw [principalList, if_neg (not_le_of_gt h)]

theorem principalList_root (m : Nat) (a : RelativeTerm Parameter) :
    .theta m a ∈ principalList m (.theta m a) := by
  rw [principalList_theta_same]
  exact List.mem_cons_self

theorem principalList_nested (m : Nat) (a s : RelativeTerm Parameter)
    (hs : s ∈ principalList m a) : s ∈ principalList m (.theta m a) := by
  rw [principalList_theta_same]
  exact List.mem_cons_of_mem _ hs

theorem principalList_toFinset [DecidableEq Parameter] (m : Nat) (t : RelativeTerm Parameter) :
    (principalList m t).toFinset = (t.subtermsAt m).filter (isThetaAt m) := by
  induction t with
  | parameter p => simp [principalList, subtermsAt, Finset.filter_singleton, isThetaAt]
  | sum a b iha ihb =>
    simp [principalList, subtermsAt, Finset.filter_insert, isThetaAt, iha, ihb,
      Finset.filter_union]
  | theta k a ih =>
    by_cases hmk : m ≤ k <;> by_cases hkm : k = m <;>
      simp [principalList, subtermsAt, Finset.filter_insert, Finset.filter_singleton,
        isThetaAt, hmk, hkm, ih]

theorem principalList_mem_iff [DecidableEq Parameter] (m : Nat)
    (t s : RelativeTerm Parameter) : s ∈ principalList m t ↔ s ∈ t.subtermsAt m ∧ isThetaAt m s := by
  rw [← List.mem_toFinset, principalList_toFinset, Finset.mem_filter]

theorem principalList_shape [DecidableEq Parameter] (m : Nat) (t s : RelativeTerm Parameter)
    (hs : s ∈ principalList m t) : ∃ a, s = .theta m a := by
  have hshape := ((principalList_mem_iff m t s).mp hs).2
  cases s with
  | parameter p => exact False.elim hshape
  | sum a b => exact False.elim hshape
  | theta k a =>
    have hk : k = m := hshape
    subst k
    exact ⟨a, rfl⟩

theorem subtermsAt_size_le [DecidableEq Parameter] (m : Nat) (t s : RelativeTerm Parameter)
    (hs : s ∈ t.subtermsAt m) : s.size ≤ t.size := by
  revert hs
  induction t with
  | parameter p =>
    intro hs
    have he : s = .parameter p := by simpa only [subtermsAt, Finset.mem_singleton] using hs
    subst s
    exact le_rfl
  | sum a b iha ihb =>
    intro hs
    rcases Finset.mem_insert.mp hs with he | hs
    · subst s; exact le_rfl
    · rcases Finset.mem_union.mp hs with hs | hs
      · exact (iha hs).trans (sum_left_size_lt a b).le
      · exact (ihb hs).trans (sum_right_size_lt a b).le
  | theta k a ih =>
    intro hs
    by_cases hmk : m ≤ k
    · rw [subtermsAt, if_pos hmk] at hs
      rcases Finset.mem_insert.mp hs with he | hs
      · subst s; exact le_rfl
      · exact (ih hs).trans (theta_arg_size_lt k a).le
    · have he : s = .theta k a := by
        simpa only [subtermsAt, if_neg hmk, Finset.mem_singleton] using hs
      subst s
      exact le_rfl

theorem principalList_size_le [DecidableEq Parameter] (m : Nat) (t s : RelativeTerm Parameter)
    (hs : s ∈ principalList m t) : s.size ≤ t.size :=
  subtermsAt_size_le m t s ((principalList_mem_iff m t s).mp hs).1

theorem principalList_argument_size_lt [DecidableEq Parameter] (m k : Nat) (a s : RelativeTerm Parameter)
    (hs : s ∈ principalList m a) : s.size < (.theta k a : RelativeTerm Parameter).size :=
  (principalList_size_le m a s hs).trans_lt (theta_arg_size_lt k a)

theorem subtermsAt_admissible [DecidableEq Parameter]
    {parameters : Parameter → Ordinal} {omega : Nat → Ordinal}
    {theta : Nat → Ordinal → Ordinal} {n b : Nat} {t s : RelativeTerm Parameter}
    (ht : Admissible parameters omega theta n b t) (m : Nat) (hs : s ∈ t.subtermsAt m) :
    Admissible parameters omega theta n b s := by
  revert hs
  induction ht with
  | @parameter p hp =>
    intro hs
    have he : s = .parameter p := by simpa only [subtermsAt, Finset.mem_singleton] using hs
    subst s
    exact .parameter hp
  | @sum a c ha hc iha ihc =>
    intro hs
    rcases Finset.mem_insert.mp hs with he | hs
    · subst s; exact .sum ha hc
    · rcases Finset.mem_union.mp hs with hs | hs
      · exact iha hs
      · exact ihc hs
  | @theta k a hbk hkn hsort ha ih =>
    intro hs
    by_cases hmk : m ≤ k
    · rw [subtermsAt, if_pos hmk] at hs
      rcases Finset.mem_insert.mp hs with he | hs
      · subst s; exact .theta hbk hkn hsort ha
      · exact ih hs
    · have he : s = .theta k a := by
        simpa only [subtermsAt, if_neg hmk, Finset.mem_singleton] using hs
      subst s
      exact .theta hbk hkn hsort ha

theorem principalList_admissible [DecidableEq Parameter]
    {parameters : Parameter → Ordinal} {omega : Nat → Ordinal}
    {theta : Nat → Ordinal → Ordinal} {n b : Nat} {t s : RelativeTerm Parameter}
    (ht : Admissible parameters omega theta n b t) (m : Nat) (hs : s ∈ principalList m t) :
    Admissible parameters omega theta n b s :=
  subtermsAt_admissible ht m ((principalList_mem_iff m t s).mp hs).1

theorem subtermsAt_normalSums [DecidableEq Parameter]
    {τ : Ordinal.{0}} {parameters : Parameter → Ordinal.{0}} {n : Nat} {t s : RelativeTerm Parameter}
    (ht : NormalSums τ parameters n t) (m : Nat) (hs : s ∈ t.subtermsAt m) :
    NormalSums τ parameters n s := by
  revert ht hs
  induction t with
  | parameter p =>
    intro ht hs
    have he : s = .parameter p := by simpa only [subtermsAt, Finset.mem_singleton] using hs
    subst s; exact ht
  | sum a b iha ihb =>
    intro ht hs
    rcases Finset.mem_insert.mp hs with he | hs
    · subst s; exact ht
    · rcases Finset.mem_union.mp hs with hs | hs
      · exact iha ht.1 hs
      · exact ihb ht.2.1 hs
  | theta k a ih =>
    intro ht hs
    by_cases hmk : m ≤ k
    · rw [subtermsAt, if_pos hmk] at hs
      rcases Finset.mem_insert.mp hs with he | hs
      · subst s; exact ht
      · exact ih ht hs
    · have he : s = .theta k a := by
        simpa only [subtermsAt, if_neg hmk, Finset.mem_singleton] using hs
      subst s; exact ht

theorem principalList_normalSums [DecidableEq Parameter]
    {τ : Ordinal.{0}} {parameters : Parameter → Ordinal.{0}} {n : Nat} {t s : RelativeTerm Parameter}
    (ht : NormalSums τ parameters n t) (m : Nat) (hs : s ∈ principalList m t) :
    NormalSums τ parameters n s :=
  subtermsAt_normalSums ht m ((principalList_mem_iff m t s).mp hs).1

theorem subtermsAt_sourceNormal [DecidableEq Parameter]
    {τ base : Ordinal.{0}} {parameters : Parameter → Ordinal.{0}} {n : Nat} {t s : RelativeTerm Parameter}
    (ht : SourceNormal τ parameters n base t) (m : Nat) (hs : s ∈ t.subtermsAt m) :
    SourceNormal τ parameters n base s := by
  revert ht hs
  induction t with
  | parameter p =>
    intro ht hs
    have he : s = .parameter p := by simpa only [subtermsAt, Finset.mem_singleton] using hs
    subst s; exact ht
  | sum a b iha ihb =>
    intro ht hs
    rcases Finset.mem_insert.mp hs with he | hs
    · subst s; exact ht
    · rcases Finset.mem_union.mp hs with hs | hs
      · exact iha ht.1 hs
      · exact ihb ht.2.1 hs
  | theta k a ih =>
    intro ht hs
    by_cases hmk : m ≤ k
    · rw [subtermsAt, if_pos hmk] at hs
      rcases Finset.mem_insert.mp hs with he | hs
      · subst s; exact ht
      · exact ih ht hs
    · have he : s = .theta k a := by
        simpa only [subtermsAt, if_neg hmk, Finset.mem_singleton] using hs
      subst s; exact ht

theorem principalList_sourceNormal [DecidableEq Parameter]
    {τ base : Ordinal.{0}} {parameters : Parameter → Ordinal.{0}} {n : Nat} {t s : RelativeTerm Parameter}
    (ht : SourceNormal τ parameters n base t) (m : Nat) (hs : s ∈ principalList m t) :
    SourceNormal τ parameters n base s :=
  subtermsAt_sourceNormal ht m ((principalList_mem_iff m t s).mp hs).1

theorem exposed_mem_principalList [DecidableEq Parameter] (m : Nat) (t s : RelativeTerm Parameter)
    (hs : s ∈ exposedThetaList m t) : s ∈ principalList m t := by
  revert hs
  induction t with
  | parameter p => intro hs; simp only [exposedThetaList, List.not_mem_nil] at hs
  | sum a b iha ihb =>
    intro hs
    rcases List.mem_append.mp hs with hs | hs
    · exact List.mem_append.mpr (Or.inl (iha hs))
    · exact List.mem_append.mpr (Or.inr (ihb hs))
  | theta k a ih =>
    intro hs
    by_cases hkm : k = m
    · subst k
      have he : s = .theta m a := by
        simpa only [exposedThetaList, if_pos rfl, if_true, List.mem_singleton] using hs
      subst s
      exact principalList_root m a
    · by_cases hmk : m < k
      · rw [principalList_theta_higher m k a hmk]
        apply ih
        simpa only [exposedThetaList, if_neg hkm, if_pos hmk] using hs
      · simp only [exposedThetaList, if_neg hkm, if_neg hmk, List.not_mem_nil] at hs

/-- This is the proved source star bound on an actual theta argument. -/
theorem exposed_argument_lt [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0}) (n m : Nat)
    (a e : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 (.theta m a))
    (hn : NormalSums τ parameters n a) (he : e ∈ exposedThetaList m a) :
    e.eval parameters (sourceFiniteCollapse τ n) < (.theta m a : RelativeTerm Parameter).eval parameters
      (sourceFiniteCollapse τ n) := by
  classical
  cases ht with
  | theta h0m hmn hsort ha =>
    have hs := sourceStar_lt_sourceFiniteCollapse τ hτ n m hmn
      (sourceAdmittedOrdinal τ parameters n m hmn a ha) hsort
    rw [sourceStar_eq_exposedTheta τ hτ parameters n m hmn a ha hn] at hs
    have hm : e.eval parameters (sourceFiniteCollapse τ n) ∈
        (exposedTheta m a).image (fun t => t.eval parameters (sourceFiniteCollapse τ n)) :=
      Finset.mem_image.mpr ⟨e, (mem_exposedThetaList_iff m a e).mp he, rfl⟩
    exact (Finset.le_sup (f := id) hm).trans_lt hs

/-- Every full-depth value is below some exposed value. Nested nodes are
controlled by the genuine argument-star theorem, not by syntax size. -/
theorem principalList_dominated_by_exposed [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0}) (n m : Nat)
    (t s : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hn : NormalSums τ parameters n t) (hs : s ∈ principalList m t) :
    ∃ e ∈ exposedThetaList m t, s.eval parameters (sourceFiniteCollapse τ n) ≤
      e.eval parameters (sourceFiniteCollapse τ n) := by
  revert ht hn hs
  induction t with
  | parameter p => intro ht hn hs; simp only [principalList, List.not_mem_nil] at hs
  | sum a b iha ihb =>
    intro ht hn hs
    cases ht with
    | sum ha hb =>
      rcases List.mem_append.mp hs with hs | hs
      · obtain ⟨e, he, hle⟩ := iha ha hn.1 hs
        exact ⟨e, List.mem_append.mpr (Or.inl he), hle⟩
      · obtain ⟨e, he, hle⟩ := ihb hb hn.2.1 hs
        exact ⟨e, List.mem_append.mpr (Or.inr he), hle⟩
  | theta k a ih =>
    intro ht hn hs
    cases ht with
    | theta h0k hkn hsort ha =>
      by_cases hkm : k = m
      · subst k
        rw [principalList_theta_same] at hs
        refine ⟨.theta m a, ?_, ?_⟩
        · simp only [exposedThetaList, if_pos rfl, if_true, List.mem_singleton]
        · rcases List.mem_cons.mp hs with he | hs
          · subst s; exact le_rfl
          · obtain ⟨e, he, hle⟩ := ih ha hn hs
            exact hle.trans (exposed_argument_lt τ hτ parameters n m a e
              (.theta h0k hkn hsort ha) hn he).le
      · by_cases hmk : m < k
        · rw [principalList_theta_higher m k a hmk] at hs
          obtain ⟨e, he, hle⟩ := ih ha hn hs
          refine ⟨e, ?_, hle⟩
          simpa only [exposedThetaList, if_neg hkm, if_pos hmk] using he
        · have hkm' : k < m := by omega
          rw [principalList_theta_lower m k a hkm'] at hs
          exact False.elim (List.not_mem_nil hs)

theorem principalList_argument_lt [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0}) (n m : Nat)
    (a s : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 (.theta m a))
    (hn : NormalSums τ parameters n a) (hs : s ∈ principalList m a) :
    s.eval parameters (sourceFiniteCollapse τ n) < (.theta m a : RelativeTerm Parameter).eval parameters
      (sourceFiniteCollapse τ n) := by
  have ha : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 a := by
    cases ht with
    | theta h0m hmn hsort ha => exact ha
  obtain ⟨e, he, hle⟩ := principalList_dominated_by_exposed τ hτ parameters n m a s ha hn hs
  exact hle.trans_lt (exposed_argument_lt τ hτ parameters n m a e ht hn he)

theorem principalList_theta_value_le [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0}) (n m : Nat)
    (a s : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 (.theta m a))
    (hn : NormalSums τ parameters n a) (hs : s ∈ principalList m (.theta m a)) :
    s.eval parameters (sourceFiniteCollapse τ n) ≤ (.theta m a : RelativeTerm Parameter).eval parameters
      (sourceFiniteCollapse τ n) := by
  rw [principalList_theta_same] at hs
  rcases List.mem_cons.mp hs with he | hs
  · subst s; exact le_rfl
  · exact (principalList_argument_lt τ hτ parameters n m a s ht hn hs).le

theorem parameterList_toFinset [DecidableEq Parameter] (t : RelativeTerm Parameter) :
    (parameterList t).toFinset = t.parameters := by
  induction t <;> simp_all [parameterList, RelativeTerm.parameters]

theorem parameterList_mem_iff [DecidableEq Parameter] (t : RelativeTerm Parameter) (p : Parameter) :
    p ∈ parameterList t ↔ p ∈ t.parameters := by
  rw [← List.mem_toFinset, parameterList_toFinset]

theorem parameterList_below [DecidableEq Parameter]
    {parameters : Parameter → Ordinal} {omega : Nat → Ordinal}
    {theta : Nat → Ordinal → Ordinal} {n b : Nat} {t : RelativeTerm Parameter}
    (ht : Admissible parameters omega theta n b t) {p : Parameter} (hp : p ∈ parameterList t) :
    parameters p < omega b := ht.parameters_below ((parameterList_mem_iff t p).mp hp)

/-- The full maximum from Definition 2.23, with the empty maximum zero. -/
noncomputable def fullStar (τ : Ordinal.{0}) (parameters : Parameter → Ordinal.{0})
    (n m : Nat) (t : RelativeTerm Parameter) : Ordinal.{0} := by
  classical
  exact ((principalList m t).map (fun s => s.eval parameters (sourceFiniteCollapse τ n))).toFinset.sup id

theorem fullStar_eq_sourceStar [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0})
    (n m : Nat) (hm : m < n) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hn : NormalSums τ parameters n t) :
    fullStar τ parameters n m t = sourceStar τ hτ n m hm
      (sourceAdmittedOrdinal τ parameters n m hm t ht) := by
  classical
  rw [fullStar, sourceStar_eq_exposedTheta τ hτ parameters n m hm t ht hn]
  apply le_antisymm
  · apply Finset.sup_le
    intro p hp
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    obtain ⟨e, he, hle⟩ := principalList_dominated_by_exposed τ hτ parameters n m t s ht hn hs
    exact hle.trans (Finset.le_sup (f := id) (Finset.mem_image.mpr
      ⟨e, (mem_exposedThetaList_iff m t e).mp he, rfl⟩))
  · apply Finset.sup_le
    intro p hp
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
    have hl := exposed_mem_principalList m t e ((mem_exposedThetaList_iff m t e).mpr he)
    exact Finset.le_sup (f := id) (List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, hl, rfl⟩))

/-- A genuine source sum with nonzero prefix is not additive principal. -/
theorem sourceNormalSum_not_principal {ξ α β : Ordinal.{0}}
    (hs : SourceNormalSum ξ α β) (hα : 0 < α) : ¬ Ordinal.IsPrincipal (· + ·) ξ := by
  intro hp
  rcases hs with ⟨hξ, ha, hb⟩ | ⟨xs, hxs, ha, hξ⟩
  · exact (ne_of_gt hα) ha
  · have hpos : 0 < ξ := by
      rw [← hξ, principalSum_append, ha]
      exact hα.trans_le le_self_add
    have he : xs ++ [β] = [ξ] :=
      (canonicalANF_eq_of_normal hxs hξ).symm.trans (canonicalANF_principal hpos hp)
    have hlen := congrArg List.length he
    have hz : xs.length = 0 := by
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    have hnil : xs = [] := List.length_eq_zero_iff.mp hz
    rw [hnil, principalSum] at ha
    exact (ne_of_gt hα) ha.symm

theorem principal_range_iff_theta
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0})
    (n m : Nat) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hn : SourceNormal τ parameters n τ t) : isThetaAt m t ↔
      0 < t.eval parameters (sourceFiniteCollapse τ n) ∧
      Ordinal.IsPrincipal (· + ·) (t.eval parameters (sourceFiniteCollapse τ n)) ∧
      omegaSequence τ m ≤ t.eval parameters (sourceFiniteCollapse τ n) ∧
      t.eval parameters (sourceFiniteCollapse τ n) < omegaSequence τ (m + 1) := by
  cases ht with
  | parameter hp =>
    constructor
    · intro hf; exact False.elim hf
    · intro hv
      exact False.elim (hp.not_ge
        (((omegaSequence_strictMono τ).monotone (Nat.zero_le m)).trans hv.2.2.1))
  | @sum a b ha hb =>
    constructor
    · intro hf; exact False.elim hf
    · intro hv
      exact False.elim (sourceNormalSum_not_principal hn.2.2.2.2 hn.2.2.1 hv.2.1)
  | @theta k a h0k hkn hsort ha =>
    have hr := source_theta_range τ parameters n k a hkn ha hsort
    constructor
    · intro hk
      have he : k = m := hk
      subst k
      exact ⟨sourceFiniteCollapse_pos τ hτ n m hkn _,
        sourceFiniteCollapse_add_closed τ n m hkn _, hr⟩
    · intro hv
      change k = m
      by_contra he
      rcases lt_or_gt_of_ne he with hkm | hmk
      · exact (hr.2.trans_le ((omegaSequence_strictMono τ).monotone
          (Nat.succ_le_of_lt hkm))).not_ge hv.2.2.1
      · exact hv.2.2.2.not_ge (((omegaSequence_strictMono τ).monotone
          (Nat.succ_le_of_lt hmk)).trans hr.1)

/-- Literal source subterms mapped to their actual ordinal values. -/
noncomputable def literalSubterms [DecidableEq Parameter]
    (τ : Ordinal.{0}) (parameters : Parameter → Ordinal.{0}) (n m : Nat)
    (t : RelativeTerm Parameter) : Finset Ordinal.{0} := by
  classical
  exact (t.subtermsAt m).image (fun s => s.eval parameters (sourceFiniteCollapse τ n))

/-- Exactly Sub_m intersect P intersect [Omega_m,Omega_(m+1)). -/
noncomputable def sourcePrincipalSupport [DecidableEq Parameter]
    (τ : Ordinal.{0}) (parameters : Parameter → Ordinal.{0}) (n m : Nat)
    (t : RelativeTerm Parameter) : Finset Ordinal.{0} := by
  classical
  exact (literalSubterms τ parameters n m t).filter (fun p =>
    0 < p ∧ Ordinal.IsPrincipal (· + ·) p ∧ omegaSequence τ m ≤ p ∧ p < omegaSequence τ (m + 1))

theorem source_definition_2_23 [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0}) (n m : Nat)
    (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hn : SourceNormal τ parameters n τ t) :
    sourcePrincipalSupport τ parameters n m t =
      ((principalList m t).map (fun s => s.eval parameters (sourceFiniteCollapse τ n))).toFinset := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hp, hclass⟩ := Finset.mem_filter.mp hp
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hp
    have hc : isThetaAt m s := (principal_range_iff_theta τ hτ parameters n m s
      (subtermsAt_admissible ht m hs) (subtermsAt_sourceNormal hn m hs)).mpr (by rw [he]; exact hclass)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨s, (principalList_mem_iff m t s).mpr ⟨hs, hc⟩, he⟩)
  · intro hp
    obtain ⟨s, hs, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    have htshape := (principalList_mem_iff m t s).mp hs
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨s, htshape.1, he⟩, ?_⟩
    rw [← he]
    exact (principal_range_iff_theta τ hτ parameters n m s
      (principalList_admissible ht m hs) (principalList_sourceNormal hn m hs)).mp htshape.2

/-- Full P_m and finite P^n_m need not be equal as sets; their actual
maxima agree, as in Remark 2.25(3). -/
theorem sourcePrincipalSupport_star [DecidableEq Parameter]
    (τ : Ordinal.{0}) (hτ : 0 < τ) (parameters : Parameter → Ordinal.{0})
    (n m : Nat) (hm : m < n) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hn : SourceNormal τ parameters n τ t) :
    (sourcePrincipalSupport τ parameters n m t).sup id =
      sourceStar τ hτ n m hm (sourceAdmittedOrdinal τ parameters n m hm t ht) := by
  rw [source_definition_2_23 τ hτ parameters n m t ht hn]
  exact fullStar_eq_sourceStar τ hτ parameters n m hm t ht hn.normalSums

theorem parameter_mem_subterms_zero [DecidableEq Parameter]
    (t : RelativeTerm Parameter) (p : Parameter) : .parameter p ∈ t.subtermsAt 0 ↔ p ∈ t.parameters := by
  induction t <;> simp_all [subtermsAt, RelativeTerm.parameters]

theorem below_base_parameter (τ : Ordinal.{0}) (parameters : Parameter → Ordinal.{0})
    (n : Nat) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hn : SourceNormal τ parameters n τ t)
    (hlow : t.eval parameters (sourceFiniteCollapse τ n) < τ) : ∃ p, t = .parameter p := by
  cases ht with
  | parameter hp => exact ⟨_, rfl⟩
  | sum ha hb => exact False.elim (hlow.not_ge hn.2.2.2.1.le)
  | @theta k a h0k hkn hsort ha =>
    have hr := (source_theta_range τ parameters n k a hkn ha hsort).1
    exact False.elim (hlow.not_ge (((omegaSequence_strictMono τ).monotone (Nat.zero_le k)).trans hr))

/-- Exactly Sub_0 intersect tau; atomic parameters remain whole ordinals. -/
noncomputable def sourceParameterSupport [DecidableEq Parameter]
    (τ : Ordinal.{0}) (parameters : Parameter → Ordinal.{0}) (n : Nat)
    (t : RelativeTerm Parameter) : Finset Ordinal.{0} := by
  classical
  exact (literalSubterms τ parameters n 0 t).filter (fun p => p < τ)

theorem source_definition_2_23_parameters [DecidableEq Parameter]
    (τ : Ordinal.{0}) (parameters : Parameter → Ordinal.{0}) (n : Nat) (t : RelativeTerm Parameter)
    (ht : Admissible parameters (omegaSequence τ) (sourceFiniteCollapse τ n) n 0 t)
    (hn : SourceNormal τ parameters n τ t) :
    sourceParameterSupport τ parameters n t = ((parameterList t).map parameters).toFinset := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hp, hlow⟩ := Finset.mem_filter.mp hp
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hp
    obtain ⟨a, ha⟩ := below_base_parameter τ parameters n s
      (subtermsAt_admissible ht 0 hs) (subtermsAt_sourceNormal hn 0 hs) (by rw [he]; exact hlow)
    subst s
    have ham : a ∈ parameterList t := (parameterList_mem_iff t a).mpr
      ((parameter_mem_subterms_zero t a).mp hs)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ham, he⟩)
  · intro hp
    obtain ⟨a, ha, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨.parameter a, (parameter_mem_subterms_zero t a).mpr
      ((parameterList_mem_iff t a).mp ha), he⟩, ?_⟩
    rw [← he]
    exact parameterList_below ht ha

/-- The explicit convention that zero is a parameter-free constant. This
does not change the literal Sub_0-intersect-tau definition above. -/
noncomputable def sourceParameterSupportNonzero [DecidableEq Parameter]
    (τ : Ordinal.{0}) (parameters : Parameter → Ordinal.{0}) (n : Nat)
    (t : RelativeTerm Parameter) : Finset Ordinal.{0} := by
  classical
  exact (sourceParameterSupport τ parameters n t).erase 0

theorem sourceParameterSupportNonzero_mem [DecidableEq Parameter]
    (τ : Ordinal.{0}) (parameters : Parameter → Ordinal.{0}) (n : Nat)
    (t : RelativeTerm Parameter) (p : Ordinal.{0}) :
    p ∈ sourceParameterSupportNonzero τ parameters n t ↔
      p ≠ 0 ∧ p ∈ sourceParameterSupport τ parameters n t := by
  classical
  exact Finset.mem_erase

/-- The actual positive parameter-restriction caller in Definition 2.43
is unchanged by keeping or removing the zero constant. -/
theorem sourceParameterSupportNonzero_below_iff [DecidableEq Parameter]
    (τ : Ordinal.{0}) (parameters : Parameter → Ordinal.{0}) (n : Nat)
    (t : RelativeTerm Parameter) (σ : Ordinal.{0}) (hσ : 0 < σ) :
    (∀ p ∈ sourceParameterSupport τ parameters n t, p < σ) ↔
      ∀ p ∈ sourceParameterSupportNonzero τ parameters n t, p < σ := by
  constructor
  · intro h p hp
    exact h p ((sourceParameterSupportNonzero_mem τ parameters n t p).mp hp).2
  · intro h p hp
    by_cases hz : p = 0
    · subst p; exact hσ
    · exact h p ((sourceParameterSupportNonzero_mem τ parameters n t p).mpr ⟨hz, hp⟩)

end Alexander313.Wilken.RelativeTerm.PrincipalSupport
