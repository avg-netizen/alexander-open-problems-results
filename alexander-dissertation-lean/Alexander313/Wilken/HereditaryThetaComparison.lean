import Alexander313.Wilken.HereditaryThetaPrimitiveLists

/-!
# Executing comparison for the full hereditary normal grammar

The algorithm opens real earlier payloads, compares current theta atoms by
the actual exposed-star law, and compares sums through their constructed
principal representatives. Its fuel counts opened payloads. No semantic order
procedure, fidelity assumption or restricted arithmetic grammar is an input.

Correctness covers every old-checked, recursively normal hereditary tree at
every level. Normalization and an executing test for that recursively normal
domain are separate remaining constructions. All proof terms are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Theta

open ThetaCourse
open SourceOne.Comparison (lexLT)

private theorem bool_not_true (b : Bool) : ((!b) = true) ↔ ¬ (b = true) := by
  cases b <;> decide

private theorem ordinal_add_lt_add_left_iff (a b c : Ordinal.{0}) :
    a + b < a + c ↔ b < c := by
  constructor
  · intro h
    by_contra hbc
    exact h.not_ge (add_le_add_right (le_of_not_gt hbc) a)
  · intro h
    have hle : a + b ≤ a + c := add_le_add_right h.le a
    have hne : a + b ≠ a + c := fun he => h.ne (add_left_cancel he)
    exact lt_of_le_of_ne hle hne

/-- Lexicographic comparison of actual positive principal normal words. -/
theorem lexLT_correct {α : Type} (cmp : α → α → Bool) (value : α → Ordinal.{0})
    (as bs : List α) (has : IsAdditiveNormalForm (as.map value))
    (hbs : IsAdditiveNormalForm (bs.map value))
    (hcmp : ∀ a ∈ as, ∀ b ∈ bs,
      (cmp a b = true ↔ value a < value b) ∧ (cmp b a = true ↔ value b < value a)) :
    lexLT cmp as bs = true ↔ principalSum (as.map value) < principalSum (bs.map value) := by
  revert bs has hbs hcmp
  induction as with
  | nil =>
    intro bs has hbs hcmp
    cases bs with
    | nil => simp [lexLT, principalSum]
    | cons b bs =>
      have hb : 0 < value b := (hbs.1 _ (List.mem_cons_self)).1
      have hp : 0 < principalSum ((b :: bs).map value) := hb.trans_le le_self_add
      simpa [lexLT, principalSum] using hp
  | cons a as ih =>
    intro bs has hbs hcmp
    cases bs with
    | nil => simp [lexLT, principalSum]
    | cons b bs =>
      have hhead := hcmp a (List.mem_cons_self) b (List.mem_cons_self)
      have htail := ih bs (additiveNormalForm_tail has) (additiveNormalForm_tail hbs)
        (fun x hx y hy => hcmp x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
      simp only [lexLT, Bool.or_eq_true, Bool.and_eq_true, bool_not_true,
        hhead.1, hhead.2, htail]
      rcases lt_trichotomy (value a) (value b) with hab | hab | hba
      · have hless : principalSum ((a :: as).map value) < value b := by
          apply principalSum_lt (hbs.1 _ (List.mem_cons_self)).1
            (hbs.1 _ (List.mem_cons_self)).2
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hab
          · exact (additiveNormalForm_head_ge has hp).trans_lt hab
        have hsum : principalSum ((a :: as).map value) < principalSum ((b :: bs).map value) :=
          hless.trans_le le_self_add
        have hsum' : principalSum (value a :: as.map value) <
            principalSum (value b :: bs.map value) := hsum
        simp [hab, hsum']
      · simp only [hab, lt_self_iff_false, not_false_eq_true, false_or, true_and,
          List.map_cons, principalSum]
        exact (ordinal_add_lt_add_left_iff (value b)
          (principalSum (as.map value)) (principalSum (bs.map value))).symm
      · have hless : principalSum ((b :: bs).map value) < value a := by
          apply principalSum_lt (has.1 _ (List.mem_cons_self)).1
            (has.1 _ (List.mem_cons_self)).2
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hba
          · exact (additiveNormalForm_head_ge hbs hp).trans_lt hba
        have hsum : principalSum ((b :: bs).map value) < principalSum ((a :: as).map value) :=
          hless.trans_le le_self_add
        have hsum' : principalSum (value b :: bs.map value) <
            principalSum (value a :: as.map value) := hsum
        simp [hba, not_lt_of_gt hba, not_lt_of_gt hsum']

def lessFuel : Nat → Nat → RelativeTerm Nat → RelativeTerm Nat → Bool
  | 0, _, _, _ => false
  | fuel + 1, 0, .parameter _, .parameter _ => false
  | fuel + 1, r + 1, .parameter p, .parameter q =>
      lessFuel fuel r (rawTree p) (rawTree q)
  | fuel + 1, _, .parameter _, .theta _ _ => true
  | fuel + 1, _, .theta _ _, .parameter _ => false
  | fuel + 1, r, .theta k a, .theta l b =>
      if k < l then true else if l < k then false else
        (lessFuel fuel r a b && (exposedThetaList k a).all
          (fun q => lessFuel fuel r q (.theta l b))) ||
        (exposedThetaList k b).any (fun q => !lessFuel fuel r q (.theta k a))
  | fuel + 1, r, t, u => lexLT (lessFuel fuel r) (atoms r t) (atoms r u)

@[simp] theorem denote_parameter_succ (r p : Nat) :
    denote (r + 1) (.parameter p) = denote r (rawTree p) := by
  cases r <;> rfl

theorem checked_parameter_payload (r p : Nat)
    (hp : check (r + 1) (.parameter p) = true) : check r (rawTree p) = true := by
  have hlow : lowCheckCode r p = true := by
    simpa only [check, finiteCheck_parameter, parameterCheck_succ] using hp
  obtain ⟨u, hu, huc⟩ := (lowCheckCode_iff r p).mp hlow
  rw [← hu, rawTree_code]
  exact (Bool.and_eq_true_iff.mp huc).1

private theorem atoms_sum_size_lt (r : Nat) (a b s : RelativeTerm Nat)
    (hs : s ∈ atoms r (.sum a b)) :
    expandedSize r s.code < expandedSize r (.sum a b : RelativeTerm Nat).code := by
  rw [atoms_sum] at hs
  rcases List.mem_append.mp hs with hs | hs
  · exact (Effective.atoms_expandedSize_le r a s hs).trans_lt
      (ThetaCourse.sum_left_size_lt r a b)
  · exact (Effective.atoms_expandedSize_le r b s hs).trans_lt
      (ThetaCourse.sum_right_size_lt r a b)

/-- Every recursive query strictly shrinks the combined expanded measure.
The input domain is the entire old grammar with actual hereditary normality. -/
theorem lessFuel_correct (fuel r : Nat) (t u : RelativeTerm Nat)
    (ht : check r t = true) (hu : check r u = true) (hnt : Normal r t) (hnu : Normal r u)
    (hbudget : expandedSize r t.code + expandedSize r u.code ≤ fuel) :
    lessFuel fuel r t u = true ↔ denote r t < denote r u := by
  induction fuel generalizing r t u with
  | zero =>
    have htpos := level_lt_expandedSize r t.code
    have hup := level_lt_expandedSize r u.code
    omega
  | succ fuel ih =>
    let n := max (SourceOne.PublicCodes.fragment t) (SourceOne.PublicCodes.fragment u)
    have htn : admissible r n t := checked_admissible r n t ht
      ((SourceOne.PublicCodes.height_le_fragment t).trans (le_max_left _ _))
    have hun : admissible r n u := checked_admissible r n u hu
      ((SourceOne.PublicCodes.height_le_fragment u).trans (le_max_right _ _))
    have lex_case (x y : RelativeTerm Nat) (hx : check r x = true) (hy : check r y = true)
        (hnx : Normal r x) (hny : Normal r y)
        (hsmall : ∀ a ∈ atoms r x, ∀ b ∈ atoms r y,
          expandedSize r a.code + expandedSize r b.code ≤ fuel) :
        lexLT (lessFuel fuel r) (atoms r x) (atoms r y) = true ↔ denote r x < denote r y := by
      let m := max (SourceOne.PublicCodes.fragment x) (SourceOne.PublicCodes.fragment y)
      have hxm := checked_admissible r m x hx
        ((SourceOne.PublicCodes.height_le_fragment x).trans (le_max_left _ _))
      have hym := checked_admissible r m y hy
        ((SourceOne.PublicCodes.height_le_fragment y).trans (le_max_right _ _))
      have hc : ∀ a ∈ atoms r x, ∀ b ∈ atoms r y,
          (lessFuel fuel r a b = true ↔ denote r a < denote r b) ∧
          (lessFuel fuel r b a = true ↔ denote r b < denote r a) := by
        intro a ha b hb
        have has := (atoms_spec r m x hxm hnx).1 a ha
        have hbs := (atoms_spec r m y hym hny).1 b hb
        have hab := hsmall a ha b hb
        exact ⟨ih r a b (admitted_checked has.1) (admitted_checked hbs.1)
          has.2 hbs.2 hab, ih r b a (admitted_checked hbs.1) (admitted_checked has.1)
          hbs.2 has.2 (by omega)⟩
      have he := lexLT_correct (lessFuel fuel r) (denote r) (atoms r x) (atoms r y)
        (atoms_denote_normal r m x hxm hnx) (atoms_denote_normal r m y hym hny) hc
      simpa only [atoms_denote_sum r m x hxm hnx, atoms_denote_sum r m y hym hny] using he
    cases t with
    | parameter p =>
      cases u with
      | parameter q =>
        cases r with
        | zero =>
          have hp : p = 0 := by
            simpa only [Payloads, parameterCheck_zero, beq_iff_eq] using htn.1
          have hq : q = 0 := by
            simpa only [Payloads, parameterCheck_zero, beq_iff_eq] using hun.1
          subst p
          subst q
          simp [lessFuel]
        | succ r =>
          have hprev := ih r (rawTree p) (rawTree q)
            (checked_parameter_payload r p ht) (checked_parameter_payload r q hu)
            ((normal_parameter_succ r p).mp hnt) ((normal_parameter_succ r q).mp hnu)
            (by
              have hp := parameter_payload_size_lt r p
              have hq := parameter_payload_size_lt r q
              omega)
          simpa only [lessFuel, denote_parameter_succ] using hprev
      | theta k a =>
        have hv := parameter_before_theta r n p k a htn hun
        rw [← denote_eq_finite r n (.parameter p) htn.2,
          ← denote_eq_finite r n (.theta k a) hun.2] at hv
        simpa [lessFuel] using hv
      | sum a b =>
        simp only [lessFuel]
        apply lex_case (.parameter p) (.sum a b) ht hu hnt hnu
        intro x hx y hy
        have hsx := Effective.atoms_expandedSize_le r (.parameter p) x hx
        have hsy := atoms_sum_size_lt r a b y hy
        omega
    | sum a b =>
      simp only [lessFuel]
      apply lex_case (.sum a b) u ht hu hnt hnu
      intro x hx y hy
      have hsx := atoms_sum_size_lt r a b x hx
      have hsy := Effective.atoms_expandedSize_le r u y hy
      omega
    | theta k a =>
      cases u with
      | parameter p =>
        have hv := parameter_before_theta r n p k a hun htn
        rw [← denote_eq_finite r n (.parameter p) hun.2,
          ← denote_eq_finite r n (.theta k a) htn.2] at hv
        simpa [lessFuel] using not_lt_of_gt hv
      | sum b c =>
        simp only [lessFuel]
        apply lex_case (.theta k a) (.sum b c) ht hu hnt hnu
        intro x hx y hy
        have hsx := Effective.atoms_expandedSize_le r (.theta k a) x hx
        have hsy := atoms_sum_size_lt r b c y hy
        omega
      | theta l b =>
        by_cases hkl : k < l
        · have hv := theta_lt_of_level_lt r n k l a b htn hun hkl
          rw [← denote_eq_finite r n (.theta k a) htn.2,
            ← denote_eq_finite r n (.theta l b) hun.2] at hv
          simpa [lessFuel, hkl] using hv
        · by_cases hlk : l < k
          · have hv := theta_lt_of_level_lt r n l k b a hun htn hlk
            rw [← denote_eq_finite r n (.theta k a) htn.2,
              ← denote_eq_finite r n (.theta l b) hun.2] at hv
            simpa [lessFuel, hkl, hlk] using not_lt_of_gt hv
          · have he : l = k := by omega
            subst l
            have haa := admitted_theta_argument htn
            have hbb := admitted_theta_argument hun
            have hna := (normal_theta r k a).mp hnt
            have hnb := (normal_theta r k b).mp hnu
            have hab := ih r a b (admitted_checked haa) (admitted_checked hbb) hna hnb
              (by simp only [expandedSize_theta] at hbudget; omega)
            have hall : (exposedThetaList k a).all
                (fun q => lessFuel fuel r q (.theta k b)) = true ↔
                ∀ q ∈ exposedThetaList k a, denote r q < denote r (.theta k b) := by
              rw [List.all_eq_true]
              apply forall_congr'
              intro q
              apply imp_congr_right
              intro hq
              exact ih r q (.theta k b) (admitted_checked (admitted_exposedThetaList haa k hq))
                hu (hna.exposedThetaList k hq) hnu (by
                  have hs := Effective.exposedThetaList_expandedSize_le r k a q hq
                  simp only [expandedSize_theta] at hbudget ⊢
                  omega)
            have hany : (exposedThetaList k b).any
                (fun q => !lessFuel fuel r q (.theta k a)) = true ↔
                ∃ q ∈ exposedThetaList k b, denote r (.theta k a) ≤ denote r q := by
              rw [List.any_eq_true]
              apply exists_congr
              intro q
              apply and_congr_right
              intro hq
              rw [bool_not_true, ih r q (.theta k a)
                (admitted_checked (admitted_exposedThetaList hbb k hq)) ht
                (hnb.exposedThetaList k hq) hnt (by
                  have hs := Effective.exposedThetaList_expandedSize_le r k b q hq
                  simp only [expandedSize_theta] at hbudget ⊢
                  omega), not_lt]
            simp only [lessFuel, lt_self_iff_false, if_false, Bool.or_eq_true,
              Bool.and_eq_true, hab, hall, hany]
            exact (theta_global_lt_iff_exposed r n k a b htn hun hna hnb).symm

def less (r : Nat) (t u : RelativeTerm Nat) : Bool :=
  lessFuel (expandedSize r t.code + expandedSize r u.code) r t u

theorem less_correct (r : Nat) (t u : RelativeTerm Nat)
    (ht : check r t = true) (hu : check r u = true) (hnt : Normal r t) (hnu : Normal r u) :
    less r t u = true ↔ denote r t < denote r u :=
  lessFuel_correct _ r t u ht hu hnt hnu le_rfl

def equal (r : Nat) (t u : RelativeTerm Nat) : Bool := !less r t u && !less r u t

theorem equal_correct (r : Nat) (t u : RelativeTerm Nat)
    (ht : check r t = true) (hu : check r u = true) (hnt : Normal r t) (hnu : Normal r u) :
    equal r t u = true ↔ denote r t = denote r u := by
  simp only [equal, Bool.and_eq_true, bool_not_true, less_correct r t u ht hu hnt hnu,
    less_correct r u t hu ht hnu hnt, not_lt]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

def lessCode (r c d : Nat) : Bool :=
  match decode c, decode d with
  | some t, some u => less r t u
  | _, _ => false

def equalCode (r c d : Nat) : Bool :=
  match decode c, decode d with
  | some t, some u => equal r t u
  | _, _ => false

@[simp] theorem lessCode_code (r : Nat) (t u : RelativeTerm Nat) :
    lessCode r t.code u.code = less r t u := by simp only [lessCode, decode_code]

@[simp] theorem equalCode_code (r : Nat) (t u : RelativeTerm Nat) :
    equalCode r t.code u.code = equal r t u := by simp only [equalCode, decode_code]

end Alexander313.Wilken.RelativeTerm.Hereditary.Theta
