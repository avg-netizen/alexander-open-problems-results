import Alexander313.Wilken.HereditaryUniformRecognition

/-! # Uniform literal hereditary course tables

Every written sum/theta child and every opened earlier-level parameter payload
has a smaller literal raw code. A row contains all levels through a supplied
bound, so a finite course table evaluates actual hereditary folds uniformly in
both arguments. The concrete instances below compute opened constituent lists
and a fuel measure, including failed payload decodes. They do not decide ordinal
comparison or replace the old hereditary grammar. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.ThetaCourse

variable {S : Type} [Primcodable S]

/-- Constructor evaluation on literal codes, opening positive-level parameters.
    The context passed to every constructor is the actual `(level, rawCode)`. -/
def run (base : Nat → S) (leaf : (Nat × Nat) → Nat → S)
    (parameterOp : (Nat × Nat) → Nat → S → S)
    (sumOp : (Nat × Nat) → S → S → S)
    (thetaOp : (Nat × Nat) → Nat → S → S) : Nat → Nat → S
  | r, 0 => base r
  | r, c + 1 =>
    let tag := c.unpair.1
    let p := c.unpair.2
    cond (tag == 0)
      (cond (r == 0) (leaf (r, c + 1) p)
        (parameterOp (r, c + 1) p (run base leaf parameterOp sumOp thetaOp (r - 1) p)))
      (cond (tag == 1)
        (sumOp (r, c + 1) (run base leaf parameterOp sumOp thetaOp r p.unpair.1)
          (run base leaf parameterOp sumOp thetaOp r p.unpair.2))
        (cond (tag == 2)
          (thetaOp (r, c + 1) p.unpair.1
            (run base leaf parameterOp sumOp thetaOp r p.unpair.2)) (base r)))
termination_by r c => c
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le c
    have hl := Nat.unpair_left_le c.unpair.2
    have hr := Nat.unpair_right_le c.unpair.2
    omega

private def row (base : Nat → S) (leaf : (Nat × Nat) → Nat → S)
    (parameterOp : (Nat × Nat) → Nat → S → S)
    (sumOp : (Nat × Nat) → S → S → S)
    (thetaOp : (Nat × Nat) → Nat → S → S) (R c : Nat) : List S :=
  (List.range (R + 1)).map (fun r => run base leaf parameterOp sumOp thetaOp r c)

private theorem row_get (base : Nat → S) (leaf : (Nat × Nat) → Nat → S)
    (parameterOp : (Nat × Nat) → Nat → S → S)
    (sumOp : (Nat × Nat) → S → S → S)
    (thetaOp : (Nat × Nat) → Nat → S → S) (R c r : Nat) (hr : r ≤ R) :
    (row base leaf parameterOp sumOp thetaOp R c)[r]?.getD (base 0) =
      run base leaf parameterOp sumOp thetaOp r c := by
  simp [row, List.getElem?_range (Nat.lt_succ_of_le hr)]

private def fetch (default : S) (history : List (List S)) (c r : Nat) : S :=
  ((history[c]?.getD [])[r]?).getD default

private theorem fetch_primrec (default : S) : Primrec
    (fun p : List (List S) × (Nat × Nat) => fetch default p.1 p.2.1 p.2.2) := by
  have hrow : Primrec (fun p : List (List S) × (Nat × Nat) => p.1[p.2.1]?.getD []) :=
    Primrec.option_getD.comp
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.const ([] : List S))
  exact Primrec.option_getD.comp
    (Primrec.list_getElem?.comp hrow (Primrec.snd.comp Primrec.snd)) (Primrec.const default)

private def entry (base : Nat → S) (leaf : (Nat × Nat) → Nat → S)
    (parameterOp : (Nat × Nat) → Nat → S → S)
    (sumOp : (Nat × Nat) → S → S → S)
    (thetaOp : (Nat × Nat) → Nat → S → S) (history : List (List S)) (r : Nat) : S :=
  let c := history.length
  let k := c - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (c == 0) (base r)
    (cond (tag == 0)
      (cond (r == 0) (leaf (r, c) p)
        (parameterOp (r, c) p (fetch (base 0) history p (r - 1))))
      (cond (tag == 1)
        (sumOp (r, c) (fetch (base 0) history p.unpair.1 r)
          (fetch (base 0) history p.unpair.2 r))
        (cond (tag == 2)
          (thetaOp (r, c) p.unpair.1 (fetch (base 0) history p.unpair.2 r)) (base r))))

private theorem entry_primrec (base : Nat → S) (leaf : (Nat × Nat) → Nat → S)
    (parameterOp : (Nat × Nat) → Nat → S → S)
    (sumOp : (Nat × Nat) → S → S → S)
    (thetaOp : (Nat × Nat) → Nat → S → S)
    (hb : Primrec base) (hl : Primrec₂ leaf)
    (hp : Primrec (fun p : (Nat × Nat) × (Nat × S) => parameterOp p.1 p.2.1 p.2.2))
    (hs : Primrec (fun p : (Nat × Nat) × (S × S) => sumOp p.1 p.2.1 p.2.2))
    (ht : Primrec (fun p : (Nat × Nat) × (Nat × S) => thetaOp p.1 p.2.1 p.2.2)) :
    Primrec₂ (entry base leaf parameterOp sumOp thetaOp) := by
  have hc : Primrec (fun p : List (List S) × Nat => p.1.length) :=
    Primrec.list_length.comp Primrec.fst
  have hk := Primrec.nat_sub.comp hc (Primrec.const 1)
  have htag := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hpay := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hleft := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hright := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have hcontext := Primrec.snd.pair hc
  have get (f g : List (List S) × Nat → Nat) (hf : Primrec f) (hg : Primrec g) :
      Primrec (fun p : List (List S) × Nat => fetch (base 0) p.1 (f p) (g p)) :=
    (fetch_primrec (base 0)).comp (Primrec.fst.pair (hf.pair hg))
  have hprevious : Primrec (fun p : List (List S) × Nat => p.2 - 1) :=
    Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
  have test (n : Nat) := Primrec.beq.comp htag (Primrec.const n)
  exact ((Primrec.beq.comp hc (Primrec.const 0)).cond (hb.comp Primrec.snd)
    ((test 0).cond
      ((Primrec.beq.comp Primrec.snd (Primrec.const 0)).cond (hl.comp hcontext hpay)
        (hp.comp (hcontext.pair (hpay.pair (get _ _ hpay hprevious)))))
      ((test 1).cond (hs.comp (hcontext.pair
        ((get _ _ hleft Primrec.snd).pair (get _ _ hright Primrec.snd))))
        ((test 2).cond (ht.comp (hcontext.pair (hleft.pair (get _ _ hright Primrec.snd))))
          (hb.comp Primrec.snd))))).to₂

private def rowStep (base : Nat → S) (leaf : (Nat × Nat) → Nat → S)
    (parameterOp : (Nat × Nat) → Nat → S → S)
    (sumOp : (Nat × Nat) → S → S → S)
    (thetaOp : (Nat × Nat) → Nat → S → S) (R : Nat) (history : List (List S)) : List S :=
  (List.range (R + 1)).map (entry base leaf parameterOp sumOp thetaOp history)

private theorem entry_correct (base : Nat → S) (leaf : (Nat × Nat) → Nat → S)
    (parameterOp : (Nat × Nat) → Nat → S → S)
    (sumOp : (Nat × Nat) → S → S → S)
    (thetaOp : (Nat × Nat) → Nat → S → S) (R c r : Nat) (hr : r ≤ R) :
    entry base leaf parameterOp sumOp thetaOp
      ((List.range c).map (row base leaf parameterOp sumOp thetaOp R)) r =
        run base leaf parameterOp sumOp thetaOp r c := by
  cases c with
  | zero => simp [entry, run]
  | succ c =>
    have hp : c.unpair.2 < c + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le c)
    have hl : c.unpair.2.unpair.1 < c + 1 := (Nat.unpair_left_le _).trans_lt hp
    have hh : c.unpair.2.unpair.2 < c + 1 := (Nat.unpair_right_le _).trans_lt hp
    have hprevious : r - 1 ≤ R := (Nat.sub_le r 1).trans hr
    simp [entry, run, fetch, List.getElem?_range hp, List.getElem?_range hl,
      List.getElem?_range hh, row_get base leaf parameterOp sumOp thetaOp R _ r hr,
      row_get base leaf parameterOp sumOp thetaOp R _ (r - 1) hprevious]

/-- A proved course-table construction; constructor effectivity is ordinary
    composition data, not an assumed hereditary recognizer or comparator. -/
theorem run_primrec (base : Nat → S) (leaf : (Nat × Nat) → Nat → S)
    (parameterOp : (Nat × Nat) → Nat → S → S)
    (sumOp : (Nat × Nat) → S → S → S)
    (thetaOp : (Nat × Nat) → Nat → S → S)
    (hb : Primrec base) (hl : Primrec₂ leaf)
    (hp : Primrec (fun p : (Nat × Nat) × (Nat × S) => parameterOp p.1 p.2.1 p.2.2))
    (hs : Primrec (fun p : (Nat × Nat) × (S × S) => sumOp p.1 p.2.1 p.2.2))
    (ht : Primrec (fun p : (Nat × Nat) × (Nat × S) => thetaOp p.1 p.2.1 p.2.2)) :
    Primrec₂ (run base leaf parameterOp sumOp thetaOp) := by
  have hentry := entry_primrec base leaf parameterOp sumOp thetaOp hb hl hp hs ht
  have hstep : Primrec₂ (rowStep base leaf parameterOp sumOp thetaOp) := by
    have hlevels : Primrec (fun p : Nat × List (List S) => List.range (p.1 + 1)) :=
      Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)
    have he : Primrec₂ (fun p : Nat × List (List S) =>
        entry base leaf parameterOp sumOp thetaOp p.2) :=
      (hentry.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
    exact (Primrec.list_map hlevels he).to₂
  have hrow : Primrec₂ (row base leaf parameterOp sumOp thetaOp) :=
    Primrec.nat_strong_rec (row base leaf parameterOp sumOp thetaOp)
      (Primrec.option_some.comp₂ hstep) (by
        intro R c
        have heq : rowStep base leaf parameterOp sumOp thetaOp R
            ((List.range c).map (row base leaf parameterOp sumOp thetaOp R)) =
              row base leaf parameterOp sumOp thetaOp R c := by
          unfold rowStep row
          apply List.map_congr_left
          intro r hr
          exact entry_correct base leaf parameterOp sumOp thetaOp R c r
            (Nat.le_of_lt_succ (List.mem_range.mp hr))
        exact congrArg some heq)
  have h := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp hrow Primrec.fst) (Primrec.const (base 0))
  have heq : (fun p : Nat × Nat =>
      (row base leaf parameterOp sumOp thetaOp p.1 p.2)[p.1]?.getD (base 0)) =
        (fun p : Nat × Nat => run base leaf parameterOp sumOp thetaOp p.1 p.2) := by
    funext p
    exact row_get base leaf parameterOp sumOp thetaOp p.1 p.2 p.1 le_rfl
  rw [heq] at h
  exact h.to₂

/-- Size of the actually opened payload syntax. Failed raw decodes receive the
    size of a default zero tree at that level, so defaulting cannot evade fuel. -/
def expandedSize : Nat → Nat → Nat :=
  run (fun r => r + 1) (fun _ _ => 1) (fun _ _ s => s + 1)
    (fun _ s t => s + t + 1) (fun _ _ s => s + 1)

theorem expandedSize_primrec : Primrec₂ expandedSize := by
  have hp : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.2.2 + 1) :=
    Primrec.succ.comp (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun p : (Nat × Nat) × (Nat × Nat) => p.2.1 + p.2.2 + 1) :=
    Primrec.succ.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))
  exact run_primrec _ _ _ _ _ Primrec.succ (Primrec.const 1).to₂ hp hs hp

theorem expandedSize_computable : Computable₂ expandedSize := expandedSize_primrec.to_comp

@[simp] theorem expandedSize_zero (r : Nat) : expandedSize r 0 = r + 1 := by
  simp only [expandedSize, run]

@[simp] theorem expandedSize_parameter_zero (p : Nat) :
    expandedSize 0 (.parameter p : RelativeTerm Nat).code = 1 := by
  simp [expandedSize, run, code, Nat.unpair_pair]

@[simp] theorem expandedSize_parameter_succ (r p : Nat) :
    expandedSize (r + 1) (.parameter p : RelativeTerm Nat).code = expandedSize r p + 1 := by
  simp [expandedSize, run, code, Nat.unpair_pair]

@[simp] theorem expandedSize_sum (r : Nat) (a b : RelativeTerm Nat) :
    expandedSize r (.sum a b : RelativeTerm Nat).code = expandedSize r a.code + expandedSize r b.code + 1 := by
  simp [expandedSize, run, code, Nat.unpair_pair]

@[simp] theorem expandedSize_theta (r k : Nat) (a : RelativeTerm Nat) :
    expandedSize r (.theta k a : RelativeTerm Nat).code = expandedSize r a.code + 1 := by
  simp [expandedSize, run, code, Nat.unpair_pair]

theorem level_lt_expandedSize (r c : Nat) : r < expandedSize r c := by
  induction c using Nat.strong_induction_on generalizing r with
  | h c ih =>
    cases c with
    | zero => simp
    | succ c =>
      have hp : c.unpair.2 < c + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le c)
      have hl : c.unpair.2.unpair.1 < c + 1 := (Nat.unpair_left_le _).trans_lt hp
      have hr : c.unpair.2.unpair.2 < c + 1 := (Nat.unpair_right_le _).trans_lt hp
      have hprevious := ih _ hp (r - 1)
      have hleft := ih _ hl r
      have hright := ih _ hr r
      change r < run _ _ _ _ _ r (c + 1)
      by_cases h0 : c.unpair.1 = 0
      · by_cases hz : r = 0
        · simp [run, h0, hz]
        · simp only [run, show (c.unpair.1 == 0) = true from by simp [h0],
            Bool.cond_true, show (r == 0) = false from by simp [hz], Bool.cond_false]
          change r < expandedSize (r - 1) c.unpair.2 + 1
          omega
      · by_cases h1 : c.unpair.1 = 1
        · simp only [run, show (c.unpair.1 == 0) = false from by simp [h0],
            Bool.cond_false, show (c.unpair.1 == 1) = true from by simp [h1], Bool.cond_true]
          change r < expandedSize r c.unpair.2.unpair.1 +
            expandedSize r c.unpair.2.unpair.2 + 1
          omega
        · by_cases h2 : c.unpair.1 = 2
          · simp only [run, show (c.unpair.1 == 0) = false from by simp [h0],
              Bool.cond_false, show (c.unpair.1 == 1) = false from by simp [h1],
              show (c.unpair.1 == 2) = true from by simp [h2], Bool.cond_true]
            change r < expandedSize r c.unpair.2.unpair.2 + 1
            omega
          · simp [run, Bool.beq_eq_decide_eq, h0, h1, h2]

/-- Literal decoder fallback, used only for the all-raw-input fuel guarantee. -/
def rawTree (c : Nat) : RelativeTerm Nat := (decode c).getD (.parameter 0)

theorem rawTree_primrec : Primrec rawTree :=
  Primrec.option_getD.comp decode_primrec (Primrec.const (.parameter 0 : RelativeTerm Nat))

@[simp] theorem rawTree_code (t : RelativeTerm Nat) : rawTree t.code = t := by
  simp [rawTree]

theorem code_pos (t : RelativeTerm Nat) : 0 < t.code := by
  cases t <;> exact Nat.succ_pos _

theorem rawTree_code_le (c : Nat) : (rawTree c).code ≤ max c 1 := by
  have hz : (.parameter 0 : RelativeTerm Nat).code = 1 := rfl
  cases h : decode c with
  | none => simpa only [rawTree, h, Option.getD_none, hz] using le_max_right c 1
  | some t =>
    have hc := decode_sound c t h
    simpa only [rawTree, h, Option.getD_some, hc] using le_max_left c 1

theorem parameter_payload_code_le (p : Nat) :
    (rawTree p).code ≤ (.parameter p : RelativeTerm Nat).code := by
  have hp : p < (.parameter p : RelativeTerm Nat).code := by
    simpa only [code, Nat.unpair_pair] using
      Nat.lt_succ_of_le (Nat.unpair_right_le (Nat.pair 0 p))
  exact (rawTree_code_le p).trans (max_le hp.le (Nat.succ_le_of_lt (code_pos _)))

@[simp] theorem expandedSize_default (r : Nat) :
    expandedSize r (.parameter 0 : RelativeTerm Nat).code = r + 1 := by
  cases r <;> simp only [expandedSize_parameter_zero, expandedSize_parameter_succ, expandedSize_zero]

theorem rawTree_expandedSize_le (r c : Nat) :
    expandedSize r (rawTree c).code ≤ expandedSize r c := by
  cases h : decode c with
  | none =>
    simpa only [rawTree, h, Option.getD_none, expandedSize_default] using
      Nat.succ_le_of_lt (level_lt_expandedSize r c)
  | some t =>
    have hc := decode_sound c t h
    simp only [rawTree, h, Option.getD_some, hc, le_refl]

theorem parameter_payload_size_lt (r p : Nat) :
    expandedSize r (rawTree p).code < expandedSize (r + 1) (.parameter p : RelativeTerm Nat).code := by
  rw [expandedSize_parameter_succ]
  exact (rawTree_expandedSize_le r p).trans_lt (Nat.lt_succ_self _)

theorem sum_left_size_lt (r : Nat) (a b : RelativeTerm Nat) :
    expandedSize r a.code < expandedSize r (.sum a b : RelativeTerm Nat).code := by
  rw [expandedSize_sum]
  omega

theorem sum_right_size_lt (r : Nat) (a b : RelativeTerm Nat) :
    expandedSize r b.code < expandedSize r (.sum a b : RelativeTerm Nat).code := by
  rw [expandedSize_sum]
  omega

theorem theta_argument_size_lt (r k : Nat) (a : RelativeTerm Nat) :
    expandedSize r a.code < expandedSize r (.theta k a : RelativeTerm Nat).code := by
  rw [expandedSize_theta]
  omega

/-- Written constituents, recursively opening earlier-level parameter payloads.
    Unknown tags and code zero contribute no fictitious syntax node. -/
def trace : Nat → Nat → List (Nat × Nat) :=
  run (fun _ => []) (fun q _ => [q]) (fun q _ xs => q :: xs)
    (fun q xs ys => q :: (xs ++ ys)) (fun q _ xs => q :: xs)

theorem trace_primrec : Primrec₂ trace := by
  have hl : Primrec₂ (fun q : Nat × Nat => fun _ : Nat => [q]) :=
    (Primrec.list_cons.comp Primrec.fst (Primrec.const [])).to₂
  have hp : Primrec (fun p : (Nat × Nat) × (Nat × List (Nat × Nat)) => p.1 :: p.2.2) :=
    Primrec.list_cons.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun p : (Nat × Nat) × (List (Nat × Nat) × List (Nat × Nat)) =>
      p.1 :: (p.2.1 ++ p.2.2)) :=
    Primrec.list_cons.comp Primrec.fst (Primrec.list_append.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact run_primrec _ _ _ _ _ (Primrec.const []) hl hp hs hp

theorem trace_computable : Computable₂ trace := trace_primrec.to_comp

theorem trace_bounds (r c : Nat) (q : Nat × Nat) (hq : q ∈ trace r c) :
    q.1 ≤ r ∧ q.2 ≤ c := by
  induction c using Nat.strong_induction_on generalizing r with
  | h c ih =>
    cases c with
    | zero => simp [trace, run] at hq
    | succ c =>
      have hp : c.unpair.2 < c + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le c)
      have hl : c.unpair.2.unpair.1 < c + 1 := (Nat.unpair_left_le _).trans_lt hp
      have hr : c.unpair.2.unpair.2 < c + 1 := (Nat.unpair_right_le _).trans_lt hp
      change q ∈ run _ _ _ _ _ r (c + 1) at hq
      simp only [run] at hq
      by_cases h0 : c.unpair.1 = 0
      · by_cases hz : r = 0
        · simp [h0, hz] at hq
          subst q
          exact ⟨Nat.zero_le _, le_rfl⟩
        · have hm : q = (r, c + 1) ∨ q ∈ trace (r - 1) c.unpair.2 := by
            simpa [Bool.beq_eq_decide_eq, h0, hz, trace] using hq
          rcases hm with rfl | hm
          · exact ⟨le_rfl, le_rfl⟩
          · have hb := ih _ hp (r - 1) hm
            exact ⟨hb.1.trans (Nat.sub_le r 1), hb.2.trans hp.le⟩
      · by_cases h1 : c.unpair.1 = 1
        · have hm : q = (r, c + 1) ∨
              q ∈ trace r c.unpair.2.unpair.1 ∨ q ∈ trace r c.unpair.2.unpair.2 := by
            simpa [Bool.beq_eq_decide_eq, h0, h1, trace, List.mem_append] using hq
          rcases hm with rfl | hm | hm
          · exact ⟨le_rfl, le_rfl⟩
          · have hb := ih _ hl r hm
            exact ⟨hb.1, hb.2.trans hl.le⟩
          · have hb := ih _ hr r hm
            exact ⟨hb.1, hb.2.trans hr.le⟩
        · by_cases h2 : c.unpair.1 = 2
          · have hm : q = (r, c + 1) ∨ q ∈ trace r c.unpair.2.unpair.2 := by
              simpa [Bool.beq_eq_decide_eq, h0, h1, h2, trace] using hq
            rcases hm with rfl | hm
            · exact ⟨le_rfl, le_rfl⟩
            · have hb := ih _ hr r hm
              exact ⟨hb.1, hb.2.trans hr.le⟩
          · simp [Bool.beq_eq_decide_eq, h0, h1, h2] at hq

end Alexander313.Wilken.RelativeTerm.Hereditary.ThetaCourse
