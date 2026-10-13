import Alexander313.Wilken.HereditaryPublicCodes
import Alexander313.Wilken.SourceOneComparison

/-!
# True theta comparison over the full hereditary source grammar

All finite hereditary parameters are retained, including parameters denoting
sums. The actual generic star theorem computes same-level comparison from
exposed theta nodes. The principal range separates every admitted parameter
from every current-level theta. Local normal sums are expressed with genuine
global denotations and proved equivalent to the unchanged finite predicate.

These are prerequisites for an executing hereditary comparator, not an
assumed order interface or a claim that such a comparator is constructed here.
Every proof term remains uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Theta

def GlobalNormalSums (r : Nat) : RelativeTerm Nat → Prop
  | .parameter _ => True
  | .sum a b => GlobalNormalSums r a ∧ GlobalNormalSums r b ∧
      SourceNormalSum (denote r (.sum a b)) (denote r a) (denote r b)
  | .theta _ a => GlobalNormalSums r a

theorem normalSums_iff_global (r n : Nat) (t : RelativeTerm Nat)
    (ht : Admissible (parameters r) (omegaSequence (finiteBase r))
      (sourceFiniteCollapse (finiteBase r) n) n 0 t) :
    NormalSums (finiteBase r) (parameters r) n t ↔ GlobalNormalSums r t := by
  induction ht with
  | parameter hp => rfl
  | @sum a b ha hb iha ihb =>
    change (NormalSums _ _ n a ∧ NormalSums _ _ n b ∧
      SourceNormalSum (finiteDenote r n (.sum a b)) (finiteDenote r n a)
        (finiteDenote r n b)) ↔ _
    rw [iha, ihb, ← denote_eq_finite r n (.sum a b) (.sum ha hb),
      ← denote_eq_finite r n a ha, ← denote_eq_finite r n b hb]
    rfl
  | theta h0k hkn hsort ha ih => exact ih

/-- Hereditary normality includes the actual earlier payload trees. A
parameter is locally atomic but its earlier value may have several atoms. -/
def Normal : Nat → RelativeTerm Nat → Prop
  | 0, t => GlobalNormalSums 0 t
  | r + 1, t => GlobalNormalSums (r + 1) t ∧
      ∀ p ∈ t.parameters, Normal r ((decode p).getD (.parameter 0))

theorem Normal.«local» {r : Nat} {t : RelativeTerm Nat} (h : Normal r t) :
    GlobalNormalSums r t := by
  cases r with
  | zero => exact h
  | succ r => exact h.1

theorem Normal.sum_left {r : Nat} {a b : RelativeTerm Nat} (h : Normal r (.sum a b)) :
    Normal r a := by
  cases r with
  | zero => exact h.1
  | succ r =>
    exact ⟨h.1.1, fun p hp => h.2 p (Finset.mem_union_left _ hp)⟩

theorem Normal.sum_right {r : Nat} {a b : RelativeTerm Nat} (h : Normal r (.sum a b)) :
    Normal r b := by
  cases r with
  | zero => exact h.2.1
  | succ r =>
    exact ⟨h.1.2.1, fun p hp => h.2 p (Finset.mem_union_right _ hp)⟩

theorem Normal.sum {r : Nat} {a b : RelativeTerm Nat} (ha : Normal r a) (hb : Normal r b)
    (hs : SourceNormalSum (denote r (.sum a b)) (denote r a) (denote r b)) :
    Normal r (.sum a b) := by
  cases r with
  | zero => exact ⟨ha, hb, hs⟩
  | succ r =>
    refine ⟨⟨ha.1, hb.1, hs⟩, ?_⟩
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact ha.2 p hp
    · exact hb.2 p hp

@[simp] theorem normal_theta (r k : Nat) (a : RelativeTerm Nat) :
    Normal r (.theta k a) ↔ Normal r a := by
  cases r <;> rfl

@[simp] theorem normal_parameter_succ (r p : Nat) :
    Normal (r + 1) (.parameter p) ↔ Normal r ((decode p).getD (.parameter 0)) := by
  simp [Normal, GlobalNormalSums, RelativeTerm.parameters]

theorem Normal.finite {r n : Nat} {t : RelativeTerm Nat} (hn : Normal r t)
    (ht : admissible r n t) : NormalSums (finiteBase r) (parameters r) n t :=
  (normalSums_iff_global r n t ht.2).mpr hn.«local»

theorem Normal.exposedThetaList {r : Nat} {t s : RelativeTerm Nat}
    (ht : Normal r t) (m : Nat) (hs : s ∈ exposedThetaList m t) : Normal r s := by
  revert ht hs
  induction t with
  | parameter p => intro _ hs; simp [RelativeTerm.exposedThetaList] at hs
  | sum a b iha ihb =>
    intro ht hs
    rcases List.mem_append.mp hs with hs | hs
    · exact iha ht.sum_left hs
    · exact ihb ht.sum_right hs
  | theta k a ih =>
    intro ht hs
    by_cases hkm : k = m
    · have he : s = .theta k a := by
        simpa only [RelativeTerm.exposedThetaList, if_pos hkm, List.mem_singleton] using hs
      subst s
      exact ht
    · by_cases hmk : m < k
      · apply ih ((normal_theta r k a).mp ht)
        simpa only [RelativeTerm.exposedThetaList, if_neg hkm, if_pos hmk] using hs
      · simp only [RelativeTerm.exposedThetaList, if_neg hkm, if_neg hmk, List.not_mem_nil] at hs

theorem payloads_exposedThetaList {r : Nat} {t s : RelativeTerm Nat}
    (ht : Payloads r t) (m : Nat) (hs : s ∈ exposedThetaList m t) : Payloads r s := by
  revert ht hs
  induction t with
  | parameter p => intro _ hs; simp [exposedThetaList] at hs
  | sum a b iha ihb =>
    intro ht hs
    rcases List.mem_append.mp hs with hs | hs
    · exact iha ht.1 hs
    · exact ihb ht.2 hs
  | theta k a ih =>
    intro ht hs
    by_cases hkm : k = m
    · have he : s = .theta k a := by
        simpa only [exposedThetaList, if_pos hkm, List.mem_singleton] using hs
      subst s
      exact ht
    · by_cases hmk : m < k
      · apply ih ht
        simpa only [exposedThetaList, if_neg hkm, if_pos hmk] using hs
      · simp only [exposedThetaList, if_neg hkm, if_neg hmk, List.not_mem_nil] at hs

theorem admitted_exposedThetaList {r n : Nat} {t s : RelativeTerm Nat}
    (ht : admissible r n t) (m : Nat) (hs : s ∈ exposedThetaList m t) :
    admissible r n s :=
  ⟨payloads_exposedThetaList ht.1 m hs, ht.2.exposedThetaList m hs⟩

theorem checked_admissible (r n : Nat) (t : RelativeTerm Nat)
    (ht : check r t = true) (hheight : t.height ≤ n) : admissible r n t :=
  (finiteCheck_iff r n t).mp
    (finiteCheck_transfer r (SourceOne.PublicCodes.fragment t) t ht n hheight)

theorem admitted_checked {r n : Nat} {t : RelativeTerm Nat} (ht : admissible r n t) :
    check r t = true := (check_iff_finite_admissible r t).mpr ⟨n, ht⟩

theorem admitted_theta_argument {r n k : Nat} {a : RelativeTerm Nat}
    (ht : admissible r n (.theta k a)) : admissible r n a := by
  cases ht.2 with
  | theta h0k hkn hsort ha => exact ⟨ht.1, ha⟩

theorem parameter_before_theta (r n p k : Nat) (a : RelativeTerm Nat)
    (hp : admissible r n (.parameter p)) (ha : admissible r n (.theta k a)) :
    finiteDenote r n (.parameter p) < finiteDenote r n (.theta k a) := by
  cases hp.2 with
  | parameter hp =>
    cases ha.2 with
    | theta h0k hkn hsort ha =>
      exact hp.trans_le
        (((omegaSequence_strictMono (finiteBase r)).monotone (Nat.zero_le k)).trans
          (source_theta_range (finiteBase r) (parameters r) n k a hkn ha hsort).1)

theorem theta_pos_principal (r n k : Nat) (a : RelativeTerm Nat)
    (ha : admissible r n (.theta k a)) :
    0 < finiteDenote r n (.theta k a) ∧
      Ordinal.IsPrincipal (· + ·) (finiteDenote r n (.theta k a)) := by
  cases ha.2 with
  | theta h0k hkn hsort ha =>
    exact ⟨sourceFiniteCollapse_pos (finiteBase r) (finiteBase_pos r) n k hkn _,
      sourceFiniteCollapse_add_closed (finiteBase r) n k hkn _⟩

theorem theta_lt_of_level_lt (r n k l : Nat) (a b : RelativeTerm Nat)
    (ha : admissible r n (.theta k a)) (hb : admissible r n (.theta l b))
    (hkl : k < l) :
    finiteDenote r n (.theta k a) < finiteDenote r n (.theta l b) := by
  cases ha.2 with
  | theta h0k hkn hsorta ha =>
    cases hb.2 with
    | theta h0l hln hsortb hb =>
      exact (source_theta_range (finiteBase r) (parameters r) n k a hkn ha hsorta).2.trans_le
        (((omegaSequence_strictMono (finiteBase r)).monotone (Nat.succ_le_of_lt hkl)).trans
          (source_theta_range (finiteBase r) (parameters r) n l b hln hb hsortb).1)

/-- The actual generic star comparison, with the full parameter semantics.
Every exposed query is a literal current-level theta constituent. -/
theorem theta_lt_iff_exposed (r n k : Nat) (a b : RelativeTerm Nat)
    (ha : admissible r n (.theta k a)) (hb : admissible r n (.theta k b))
    (hna : NormalSums (finiteBase r) (parameters r) n a)
    (hnb : NormalSums (finiteBase r) (parameters r) n b) :
    finiteDenote r n (.theta k a) < finiteDenote r n (.theta k b) ↔
      (finiteDenote r n a < finiteDenote r n b ∧
        ∀ q ∈ exposedThetaList k a, finiteDenote r n q < finiteDenote r n (.theta k b)) ∨
      ∃ q ∈ exposedThetaList k b, finiteDenote r n (.theta k a) ≤ finiteDenote r n q := by
  classical
  cases ha.2 with
  | theta h0k hkn hsorta ha =>
    cases hb.2 with
    | theta h0k' hkn' hsortb hb =>
      let α := sourceAdmittedOrdinal (finiteBase r) (parameters r) n k hkn a ha
      let β := sourceAdmittedOrdinal (finiteBase r) (parameters r) n k hkn b hb
      have star_lt (t : RelativeTerm Nat)
          (ht : Admissible (parameters r) (omegaSequence (finiteBase r))
            (sourceFiniteCollapse (finiteBase r) n) n 0 t)
          (hnt : NormalSums (finiteBase r) (parameters r) n t)
          (c : Ordinal.{0}) (hc : 0 < c) :
          sourceStar (finiteBase r) (finiteBase_pos r) n k hkn
            (sourceAdmittedOrdinal (finiteBase r) (parameters r) n k hkn t ht) < c ↔
              ∀ q ∈ exposedThetaList k t, finiteDenote r n q < c := by
        rw [sourceStar_eq_exposedTheta (finiteBase r) (finiteBase_pos r)
          (parameters r) n k hkn t ht hnt, Finset.sup_lt_iff hc]
        constructor
        · intro h q hq
          exact h _ (Finset.mem_image.mpr ⟨q, (mem_exposedThetaList_iff k t q).mp hq, rfl⟩)
        · intro h p hp
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
          exact h q ((mem_exposedThetaList_iff k t q).mpr hq)
      have star_le : finiteDenote r n (.theta k a) ≤
          sourceStar (finiteBase r) (finiteBase_pos r) n k hkn β ↔
            ∃ q ∈ exposedThetaList k b, finiteDenote r n (.theta k a) ≤ finiteDenote r n q := by
        change finiteDenote r n (.theta k a) ≤
          sourceStar (finiteBase r) (finiteBase_pos r) n k hkn
            (sourceAdmittedOrdinal (finiteBase r) (parameters r) n k hkn b hb) ↔ _
        rw [← not_lt, star_lt b hb hnb (finiteDenote r n (.theta k a))
          (sourceFiniteCollapse_pos (finiteBase r) (finiteBase_pos r) n k hkn _)]
        simp only [not_forall, _root_.not_imp, not_lt, exists_prop]
      have hs := sourceFiniteCollapse_lt_iff_sourceStar (finiteBase r) (finiteBase_pos r)
        n k hkn α β hsorta hsortb
      exact hs.trans (or_congr
        (and_congr Iff.rfl (star_lt a ha hna _
          (sourceFiniteCollapse_pos (finiteBase r) (finiteBase_pos r) n k hkn _))) star_le)

/-- Transport of the actual finite star law to global values. Admission of
each exposed query follows from its literal occurrence, so this transport
does not use a total collapse value outside its true source domain. -/
theorem theta_global_lt_iff_exposed (r n k : Nat) (a b : RelativeTerm Nat)
    (ha : admissible r n (.theta k a)) (hb : admissible r n (.theta k b))
    (hna : Normal r a) (hnb : Normal r b) :
    denote r (.theta k a) < denote r (.theta k b) ↔
      (denote r a < denote r b ∧
        ∀ q ∈ exposedThetaList k a, denote r q < denote r (.theta k b)) ∨
      ∃ q ∈ exposedThetaList k b, denote r (.theta k a) ≤ denote r q := by
  have haa := admitted_theta_argument ha
  have hbb := admitted_theta_argument hb
  rw [denote_eq_finite r n (.theta k a) ha.2,
    denote_eq_finite r n (.theta k b) hb.2,
    theta_lt_iff_exposed r n k a b ha hb (hna.finite haa) (hnb.finite hbb)]
  apply or_congr
  · apply and_congr
    · rw [denote_eq_finite r n a haa.2, denote_eq_finite r n b hbb.2]
    · apply forall_congr'
      intro q
      apply imp_congr_right
      intro hq
      rw [denote_eq_finite r n q (haa.2.exposedThetaList k hq)]
  · apply exists_congr
    intro q
    apply and_congr_right
    intro hq
    rw [denote_eq_finite r n q (hbb.2.exposedThetaList k hq)]

end Alexander313.Wilken.RelativeTerm.Hereditary.Theta
