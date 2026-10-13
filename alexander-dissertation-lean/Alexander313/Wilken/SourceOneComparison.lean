import Alexander313.Wilken.SourceOneComparisonSupport

/-!
# An executing comparison of admitted normal base-one trees

The Boolean program below uses only literal constructors, natural theta
levels, finite lists and decreasing fuel. Its initial fuel is the combined
node size. Same-level theta comparisons execute the proved star formula;
sum comparisons execute lexicographic comparison of the actual principal
atom lists. Correctness is proved from the constructed source functions.

This gives total executable tree/code equality and strict order on the stated
admitted normal domain. `SourceOneNormalComparison` recognizes that domain.
A uniform Primrec/Program realization and normalization of arbitrary admitted
trees remain separate work. Malformed raw codes are rejected by the decoder.
-/

namespace Alexander313.Wilken.RelativeTerm.SourceOne.Comparison

private theorem bool_not_true (b : Bool) : ((!b) = true) ↔ ¬ (b = true) := by
  cases b <;> decide

def lexLT {α : Type} (cmp : α → α → Bool) : List α → List α → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => cmp a b || (!cmp b a && lexLT cmp as bs)

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

private theorem lexLT_correct {α : Type} (cmp : α → α → Bool) (value : α → Ordinal.{0})
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

def lessFuel : Nat → RelativeTerm Nat → RelativeTerm Nat → Bool
  | 0, _, _ => false
  | fuel + 1, .theta k a, .theta l b =>
      if k < l then true else if l < k then false else
        (lessFuel fuel a b && (exposedThetaList k a).all
          (fun q => lessFuel fuel q (.theta l b))) ||
        (exposedThetaList k b).any (fun q => !lessFuel fuel q (.theta k a))
  | fuel + 1, t, u => lexLT (lessFuel fuel) (thetaAtoms t) (thetaAtoms u)

private theorem size_pos (t : RelativeTerm Nat) : 0 < t.size := by
  cases t <;> simp only [size] <;> omega

/-- Every call through an atom list shrinks when either input is a sum.
Calls through exposed nodes replace a theta input by a node in its argument.
The fuel proof below checks those inequalities separately at each call. -/
theorem lessFuel_correct (fuel n : Nat) (t u : RelativeTerm Nat)
    (ht : admissible n t) (hu : admissible n u) (hnt : Normal n t) (hnu : Normal n u)
    (hbudget : t.size + u.size ≤ fuel) :
    lessFuel fuel t u = true ↔ denote n t < denote n u := by
  induction fuel generalizing t u with
  | zero => have htpos := size_pos t; have hup := size_pos u; omega
  | succ fuel ih =>
    have lex_case (x y : RelativeTerm Nat) (hx : admissible n x) (hy : admissible n y)
        (hnx : Normal n x) (hny : Normal n y)
        (hsmall : ∀ a ∈ thetaAtoms x, ∀ b ∈ thetaAtoms y, a.size + b.size ≤ fuel) :
        lexLT (lessFuel fuel) (thetaAtoms x) (thetaAtoms y) = true ↔ denote n x < denote n y := by
      have hc : ∀ a ∈ thetaAtoms x, ∀ b ∈ thetaAtoms y,
          (lessFuel fuel a b = true ↔ denote n a < denote n b) ∧
          (lessFuel fuel b a = true ↔ denote n b < denote n a) := by
        intro a ha b hb
        have hab := hsmall a ha b hb
        exact ⟨ih a b (hx.thetaAtoms ha) (hy.thetaAtoms hb)
          (NormalSums.thetaAtoms hnx ha) (NormalSums.thetaAtoms hny hb) hab,
          ih b a (hy.thetaAtoms hb) (hx.thetaAtoms ha)
            (NormalSums.thetaAtoms hny hb) (NormalSums.thetaAtoms hnx ha) (by omega)⟩
      have he := lexLT_correct (lessFuel fuel) (denote n) (thetaAtoms x) (thetaAtoms y)
        (thetaAtoms_denote_normal n x hx hnx) (thetaAtoms_denote_normal n y hy hny) hc
      simpa only [thetaAtoms_denote_sum n x hx hnx, thetaAtoms_denote_sum n y hy hny] using he
    cases t with
    | parameter p =>
      change lexLT (lessFuel fuel) (thetaAtoms (.parameter p)) (thetaAtoms u) = true ↔ _
      apply lex_case (.parameter p) u ht hu hnt hnu
      intro a ha
      simp [thetaAtoms] at ha
    | sum a b =>
      change lexLT (lessFuel fuel) (thetaAtoms (.sum a b)) (thetaAtoms u) = true ↔ _
      apply lex_case (.sum a b) u ht hu hnt hnu
      intro x hx y hy
      have hsx := thetaAtoms_sum_size_lt a b x hx
      have hsy := thetaAtoms_size_le u y hy
      omega
    | theta k a =>
      cases u with
      | parameter p =>
        change lexLT (lessFuel fuel) (thetaAtoms (.theta k a)) (thetaAtoms (.parameter p)) = true ↔ _
        apply lex_case (.theta k a) (.parameter p) ht hu hnt hnu
        intro x hx y hy
        simp [thetaAtoms] at hy
      | sum b c =>
        change lexLT (lessFuel fuel) (thetaAtoms (.theta k a)) (thetaAtoms (.sum b c)) = true ↔ _
        apply lex_case (.theta k a) (.sum b c) ht hu hnt hnu
        intro x hx y hy
        have hsx := thetaAtoms_size_le (.theta k a) x hx
        have hsy := thetaAtoms_sum_size_lt b c y hy
        omega
      | theta l b =>
        by_cases hkl : k < l
        · have hv := theta_lt_of_level_lt n k l a b ht hu hkl
          simpa [lessFuel, hkl] using hv
        · by_cases hlk : l < k
          · have hv := theta_lt_of_level_lt n l k b a hu ht hlk
            simpa [lessFuel, hkl, hlk] using not_lt_of_gt hv
          · have he : l = k := by omega
            subst l
            cases ht with
            | theta h0k hkn hsorta ha =>
              cases hu with
              | theta h0k' hkn' hsortb hb =>
                have ht : admissible n (.theta k a) := .theta h0k hkn hsorta ha
                have hu : admissible n (.theta k b) := .theta h0k' hkn' hsortb hb
                have hab := ih a b ha hb hnt hnu (by simp only [size] at hbudget; omega)
                have hall : (exposedThetaList k a).all
                    (fun q => lessFuel fuel q (.theta k b)) = true ↔
                    ∀ q ∈ exposedThetaList k a, denote n q < denote n (.theta k b) := by
                  rw [List.all_eq_true]
                  apply forall_congr'
                  intro q
                  apply imp_congr_right
                  intro hq
                  exact ih q (.theta k b) (ha.exposedThetaList k hq) hu
                    (NormalSums.exposedThetaList (show Normal n a from hnt) k hq) hnu (by
                      have hs := exposedThetaList_size_le k a q hq
                      simp only [size] at hbudget ⊢
                      omega)
                have hany : (exposedThetaList k b).any
                    (fun q => !lessFuel fuel q (.theta k a)) = true ↔
                    ∃ q ∈ exposedThetaList k b, denote n (.theta k a) ≤ denote n q := by
                  rw [List.any_eq_true]
                  apply exists_congr
                  intro q
                  apply and_congr_right
                  intro hq
                  rw [bool_not_true, ih q (.theta k a) (hb.exposedThetaList k hq) ht
                    (NormalSums.exposedThetaList (show Normal n b from hnu) k hq) hnt (by
                      have hs := exposedThetaList_size_le k b q hq
                      simp only [size] at hbudget ⊢
                      omega), not_lt]
                simp only [lessFuel, lt_self_iff_false, if_false, Bool.or_eq_true,
                  Bool.and_eq_true, hab, hall, hany]
                exact (theta_lt_iff_exposed n k a b ht hu hnt hnu).symm

def less (t u : RelativeTerm Nat) : Bool := lessFuel (t.size + u.size) t u

theorem less_correct (n : Nat) (t u : RelativeTerm Nat)
    (ht : admissible n t) (hu : admissible n u) (hnt : Normal n t) (hnu : Normal n u) :
    less t u = true ↔ denote n t < denote n u :=
  lessFuel_correct (t.size + u.size) n t u ht hu hnt hnu le_rfl

def equal (t u : RelativeTerm Nat) : Bool := !less t u && !less u t

theorem equal_correct (n : Nat) (t u : RelativeTerm Nat)
    (ht : admissible n t) (hu : admissible n u) (hnt : Normal n t) (hnu : Normal n u) :
    equal t u = true ↔ denote n t = denote n u := by
  simp only [equal, Bool.and_eq_true, bool_not_true, less_correct n t u ht hu hnt hnu,
    less_correct n u t hu ht hnu hnt, not_lt]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

def lessCode (c d : Nat) : Bool :=
  match RelativeTerm.decode c, RelativeTerm.decode d with
  | some t, some u => less t u
  | _, _ => false

def equalCode (c d : Nat) : Bool :=
  match RelativeTerm.decode c, RelativeTerm.decode d with
  | some t, some u => equal t u
  | _, _ => false

@[simp] theorem lessCode_code (t u : RelativeTerm Nat) : lessCode t.code u.code = less t u := by
  simp only [lessCode, RelativeTerm.decode_code]

@[simp] theorem equalCode_code (t u : RelativeTerm Nat) : equalCode t.code u.code = equal t u := by
  simp only [equalCode, RelativeTerm.decode_code]

theorem less_global_correct (n : Nat) (t u : RelativeTerm Nat)
    (ht : admissible n t) (hu : admissible n u) (hnt : Normal n t) (hnu : Normal n u) :
    less t u = true ↔ PublicCodes.denote t < PublicCodes.denote u := by
  rw [PublicCodes.denote_eq_finite n t ht, PublicCodes.denote_eq_finite n u hu]
  exact less_correct n t u ht hu hnt hnu

theorem equal_global_correct (n : Nat) (t u : RelativeTerm Nat)
    (ht : admissible n t) (hu : admissible n u) (hnt : Normal n t) (hnu : Normal n u) :
    equal t u = true ↔ PublicCodes.denote t = PublicCodes.denote u := by
  rw [PublicCodes.denote_eq_finite n t ht, PublicCodes.denote_eq_finite n u hu]
  exact equal_correct n t u ht hu hnt hnu

end Alexander313.Wilken.RelativeTerm.SourceOne.Comparison
