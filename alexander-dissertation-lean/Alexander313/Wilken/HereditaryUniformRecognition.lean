import Alexander313.Wilken.HereditaryPublicCodes

/-!
# Uniform primitive-recursive hereditary recognition

A course row stores the actual admission value at every level through a
given bound. Parameter payloads, sum children and theta children all have
smaller literal codes, so every lookup uses an earlier row. Opening a
parameter decreases its level as well. The table is bounded and uses the
existing primitive-recursive literal outer-sort algorithm.

The resulting uniform algorithm is proved equal to the earlier hereditary
checkers, including their rejection of malformed syntax. This closes the
uniform PR gap for admission and the tagged finite union. It constructs no
normal form, semantic ordinal comparison, υ-index identification or edge
algorithm. All proof terms await external compilation.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Uniform

/-- Admission with all written indices already contained in the tree's own
    fragment. Each genuine theta argument still passes its exact sort test. -/
def admissionCode : Nat → Nat → Bool
  | _, 0 => false
  | r, c + 1 =>
    let tag := c.unpair.1
    let p := c.unpair.2
    cond (tag == 0)
      (cond (r == 0) (p == 0)
        (admissionCode (r - 1) p && decide (SourceOne.PublicCodes.outerSortCode p ≤ 1)))
      (cond (tag == 1)
        (admissionCode r p.unpair.1 && admissionCode r p.unpair.2)
        (cond (tag == 2)
          (admissionCode r p.unpair.2 &&
            decide (SourceOne.PublicCodes.outerSortCode p.unpair.2 ≤ p.unpair.1 + 2)) false))
termination_by r c => c
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le c
    have hl := Nat.unpair_left_le c.unpair.2
    have hr := Nat.unpair_right_le c.unpair.2
    omega

theorem admissionCode_isCode (r c : Nat) (h : admissionCode r c = true) : isCode c = true := by
  have sound : ∀ c r, admissionCode r c = true → isCode c = true := by
    intro c
    induction c using Nat.strong_induction_on with
    | h c ih =>
      intro r hc
      cases c with
      | zero => simp [admissionCode] at hc
      | succ k =>
        have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
        have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
        have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
        by_cases h0 : k.unpair.1 = 0
        · simp [isCode, h0]
        · by_cases h1 : k.unpair.1 = 1
          · have hs : admissionCode r k.unpair.2.unpair.1 = true ∧
                admissionCode r k.unpair.2.unpair.2 = true := by
              simpa [admissionCode, h0, h1, Bool.and_eq_true] using hc
            simp [isCode, h0, h1, ih _ hl r hs.1, ih _ hr r hs.2]
          · by_cases h2 : k.unpair.1 = 2
            · have hs : admissionCode r k.unpair.2.unpair.2 = true := by
                have hs' : admissionCode r k.unpair.2.unpair.2 = true ∧
                    SourceOne.PublicCodes.outerSortCode k.unpair.2.unpair.2 ≤ k.unpair.2.unpair.1 + 2 := by
                  simpa [admissionCode, h0, h1, h2, Bool.and_eq_true] using hc
                exact hs'.1
              simp [isCode, h0, h1, h2, ih _ hr r hs]
            · simp [admissionCode, h0, h1, h2] at hc
  exact sound c r h

private theorem finiteCheck_eq_check (r n : Nat) (t : RelativeTerm Nat)
    (hheight : t.height ≤ n) : finiteCheck r n t = Hereditary.check r t := by
  have hequiv : finiteCheck r n t = true ↔ Hereditary.check r t = true := by
    constructor
    · intro ht
      exact finiteCheck_transfer r n t ht (SourceOne.PublicCodes.fragment t)
        (SourceOne.PublicCodes.height_le_fragment t)
    · intro ht
      exact finiteCheck_transfer r (SourceOne.PublicCodes.fragment t) t ht n hheight
  cases h₁ : finiteCheck r n t <;> cases h₂ : Hereditary.check r t <;> simp_all

@[simp] theorem check_parameter (r p : Nat) :
    Hereditary.check r (.parameter p) = parameterCheck r p := rfl

@[simp] theorem check_sum (r : Nat) (a b : RelativeTerm Nat) :
    Hereditary.check r (.sum a b) = (Hereditary.check r a && Hereditary.check r b) := by
  let n := SourceOne.PublicCodes.fragment (.sum a b)
  have ha : a.height ≤ n := (le_max_left _ _).trans (Nat.le_succ _)
  have hb : b.height ≤ n := (le_max_right _ _).trans (Nat.le_succ _)
  change finiteCheck r n (.sum a b) = _
  rw [finiteCheck_sum, finiteCheck_eq_check r n a ha, finiteCheck_eq_check r n b hb]

@[simp] theorem check_theta (r k : Nat) (a : RelativeTerm Nat) :
    Hereditary.check r (.theta k a) =
      (Hereditary.check r a && decide (a.outerSort ≤ k + 2)) := by
  let n := SourceOne.PublicCodes.fragment (.theta k a)
  have ha : a.height ≤ n := (le_max_right _ _).trans (Nat.le_succ _)
  have hk : k < n := by
    have hk' : k + 1 ≤ max (k + 1) a.height := le_max_left _ _
    change k < max (k + 1) a.height + 1
    omega
  change finiteCheck r n (.theta k a) = _
  rw [finiteCheck_theta, finiteCheck_eq_check r n a ha]
  simp only [hk, decide_true, Bool.and_true]

private theorem typed_correct (r : Nat)
    (hp : ∀ p, admissionCode r ((.parameter p : RelativeTerm Nat).code) = parameterCheck r p) :
    ∀ t : RelativeTerm Nat, admissionCode r t.code = Hereditary.check r t := by
  intro t
  induction t with
  | parameter p => simpa only [check_parameter] using hp p
  | sum a b iha ihb =>
    simp [admissionCode, RelativeTerm.code, Nat.unpair_pair, iha, ihb, check_sum]
  | theta k a ih =>
    simp [admissionCode, RelativeTerm.code, Nat.unpair_pair, ih, check_theta,
      SourceOne.PublicCodes.outerSortCode_code]

private theorem raw_correct_of_typed (r : Nat)
    (ht : ∀ t : RelativeTerm Nat, admissionCode r t.code = Hereditary.check r t) :
    ∀ c, admissionCode r c = Hereditary.checkCode r c := by
  intro c
  by_cases hs : isCode c = true
  · obtain ⟨t, hcode⟩ := isCode_sound c hs
    simpa only [← hcode, Hereditary.checkCode_code] using ht t
  · have hsyntax : isCode c = false := by cases h : isCode c <;> simp_all
    have ha : admissionCode r c = false := by
      cases h : admissionCode r c
      · rfl
      · exact False.elim (hs (admissionCode_isCode r c h))
    simp only [ha, Hereditary.checkCode, finiteCheckCode, hsyntax, Bool.false_and]

/-- Exact equality with the earlier checker, at every level and raw code. -/
theorem admissionCode_eq (r c : Nat) : admissionCode r c = Hereditary.checkCode r c := by
  have exactLevel : ∀ r c, admissionCode r c = Hereditary.checkCode r c := by
    intro r
    induction r with
    | zero =>
      apply raw_correct_of_typed 0
      apply typed_correct 0
      intro p
      simp [admissionCode, RelativeTerm.code, Nat.unpair_pair, parameterCheck]
    | succ r ih =>
      apply raw_correct_of_typed (r + 1)
      apply typed_correct (r + 1)
      intro p
      simp [admissionCode, RelativeTerm.code, Nat.unpair_pair, parameterCheck,
        ih p, lowCheckCode_eq]
  exact exactLevel r c

private def row (r c : Nat) : List Bool :=
  (List.range (r + 1)).map (fun ℓ => admissionCode ℓ c)

private theorem row_get (r c ℓ : Nat) (hℓ : ℓ ≤ r) :
    (row r c)[ℓ]?.getD false = admissionCode ℓ c := by
  simp [row, List.getElem?_range (by omega : ℓ < r + 1)]

private def fetch (history : List (List Bool)) (c ℓ : Nat) : Bool :=
  (history[c]?.getD [])[ℓ]?.getD false

private def entry (history : List (List Bool)) (ℓ : Nat) : Bool :=
  let c := history.length - 1
  let tag := c.unpair.1
  let p := c.unpair.2
  cond (history.length == 0) false
    (cond (tag == 0)
      (cond (ℓ == 0) (p == 0)
        (fetch history p (ℓ - 1) && decide (SourceOne.PublicCodes.outerSortCode p ≤ 1)))
      (cond (tag == 1)
        (fetch history p.unpair.1 ℓ && fetch history p.unpair.2 ℓ)
        (cond (tag == 2)
          (fetch history p.unpair.2 ℓ &&
            decide (SourceOne.PublicCodes.outerSortCode p.unpair.2 ≤ p.unpair.1 + 2)) false)))

private theorem entry_primrec : Primrec₂ entry := by
  have hn : Primrec (fun p : List (List Bool) × Nat => p.1.length) :=
    Primrec.list_length.comp Primrec.fst
  have hc := Primrec.nat_sub.comp hn (Primrec.const 1)
  have htag := Primrec.fst.comp (Primrec.unpair.comp hc)
  have hpay := Primrec.snd.comp (Primrec.unpair.comp hc)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have test (n : Nat) := Primrec.beq.comp htag (Primrec.const n)
  have get (f g : List (List Bool) × Nat → Nat) (hf : Primrec f) (hg : Primrec g) :
      Primrec (fun p : List (List Bool) × Nat => fetch p.1 (f p) (g p)) := by
    have hrow := Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst hf)
      (Primrec.const ([] : List Bool))
    exact Primrec.option_getD.comp (Primrec.list_getElem?.comp hrow hg) (Primrec.const false)
  have hprev : Primrec (fun p : List (List Bool) × Nat => p.2 - 1) :=
    Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
  have hpLow := (Primrec.nat_le.comp
    (SourceOne.PublicCodes.outerSortCode_primrec.comp hpay) (Primrec.const 1)).decide
  have hsort := (Primrec.nat_le.comp
    (SourceOne.PublicCodes.outerSortCode_primrec.comp hr)
    (Primrec.nat_add.comp hl (Primrec.const 2))).decide
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const false)
    ((test 0).cond
      ((Primrec.beq.comp Primrec.snd (Primrec.const 0)).cond
        (Primrec.beq.comp hpay (Primrec.const 0))
        (Primrec.and.comp (get _ _ hpay hprev) hpLow))
      ((test 1).cond (Primrec.and.comp (get _ _ hl Primrec.snd) (get _ _ hr Primrec.snd))
        ((test 2).cond (Primrec.and.comp (get _ _ hr Primrec.snd) hsort)
          (Primrec.const false))))).to₂

private def rowStep (r : Nat) (history : List (List Bool)) : List Bool :=
  (List.range (r + 1)).map (entry history)

private theorem rowStep_primrec : Primrec₂ rowStep := by
  have hlevels : Primrec (fun p : Nat × List (List Bool) => List.range (p.1 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)
  have he : Primrec₂ (fun p : Nat × List (List Bool) => entry p.2) :=
    (entry_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_map hlevels he).to₂

private theorem entry_correct (r c ℓ : Nat) (hℓ : ℓ ≤ r) :
    entry ((List.range c).map (row r)) ℓ = admissionCode ℓ c := by
  cases c with
  | zero => simp [entry, admissionCode]
  | succ k =>
    have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
    have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
    have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
    have hprev : ℓ - 1 ≤ r := (Nat.sub_le ℓ 1).trans hℓ
    simp [entry, admissionCode, fetch, List.getElem?_range hp,
      List.getElem?_range hl, List.getElem?_range hr, row_get r _ ℓ hℓ,
      row_get r _ (ℓ - 1) hprev]

private theorem rowStep_correct (r c : Nat) :
    rowStep r ((List.range c).map (row r)) = row r c := by
  unfold rowStep row
  apply List.map_congr_left
  intro ℓ hℓ
  exact entry_correct r c ℓ (Nat.le_of_lt_succ (List.mem_range.mp hℓ))

/-- One bounded row table proves genuine primitive recursiveness uniformly
    in both the level and the literal code. -/
private theorem row_primrec : Primrec₂ row := by
  have hg := Primrec.option_some.comp₂ rowStep_primrec
  exact Primrec.nat_strong_rec row hg (by
    intro r c
    simpa only [rowStep] using congrArg some (rowStep_correct r c))

theorem admissionCode_primrec : Primrec₂ admissionCode := by
  have hget := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp row_primrec Primrec.fst) (Primrec.const false)
  have heq : (fun p : Nat × Nat => (row p.1 p.2)[p.1]?.getD false) =
      (fun p : Nat × Nat => admissionCode p.1 p.2) := by
    funext p
    exact row_get p.1 p.2 p.1 le_rfl
  rw [heq] at hget
  exact hget.to₂

theorem hereditaryCheckCode_primrec : Primrec₂ Hereditary.checkCode := by
  have heq : admissionCode = Hereditary.checkCode := by
    funext r c
    exact admissionCode_eq r c
  have h := admissionCode_primrec
  rw [heq] at h
  exact h

theorem hereditaryLowCheckCode_primrec : Primrec₂ Hereditary.lowCheckCode := by
  have hlow : Primrec (fun p : Nat × Nat =>
      Hereditary.checkCode p.1 p.2 && decide (SourceOne.PublicCodes.outerSortCode p.2 ≤ 1)) :=
    Primrec.and.comp hereditaryCheckCode_primrec
      (Primrec.nat_le.comp (SourceOne.PublicCodes.outerSortCode_primrec.comp Primrec.snd)
        (Primrec.const 1)).decide
  have heq : (fun p : Nat × Nat =>
      Hereditary.checkCode p.1 p.2 && decide (SourceOne.PublicCodes.outerSortCode p.2 ≤ 1)) =
      (fun p : Nat × Nat => Hereditary.lowCheckCode p.1 p.2) := by
    funext p
    exact (lowCheckCode_eq p.1 p.2).symm
  rw [heq] at hlow
  exact hlow.to₂

theorem unionCheck_primrec : Primrec unionCheck :=
  hereditaryLowCheckCode_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)

theorem unionCheck_computable : Computable unionCheck := unionCheck_primrec.to_comp

theorem unionCheck_primrecPred : PrimrecPred (fun c => unionCheck c = true) :=
  Primrec.eq.comp unionCheck_primrec (Primrec.const true)

end Alexander313.Wilken.RelativeTerm.Hereditary.Uniform
