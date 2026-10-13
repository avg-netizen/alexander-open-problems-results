import Alexander313.Wilken.ComparisonPrimitiveLists

/-! # A uniform primitive recursive implementation of the literal comparison

At each fuel step a finite square table stores the previous answers on all
literal codes below a chosen bound. Every actual recursive comparison stays
within that bound. Invalid table cells may use a default tree; the raw-code
operations below retain the actual decoder guards. This proves the existing
algorithms primitive recursive on all inputs, without an ordinal oracle.
The semantic correctness domain remains the admitted normal base-one trees.
Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.SourceOne.Comparison.Effective

abbrev Matrix := List (List Bool)

def lookup (table : Matrix) (t u : RelativeTerm Nat) : Bool :=
  ((table[t.code]?.getD [])[u.code]?).getD false

theorem lookup_primrec : Primrec (fun p : Matrix × (RelativeTerm Nat × RelativeTerm Nat) =>
    lookup p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Matrix × (RelativeTerm Nat × RelativeTerm Nat) => p.2.1.code) :=
    code_primrec.comp (Primrec.fst.comp Primrec.snd)
  have hu : Primrec (fun p : Matrix × (RelativeTerm Nat × RelativeTerm Nat) => p.2.2.code) :=
    code_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hrow := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp Primrec.fst ht) (Primrec.const ([] : List Bool))
  exact Primrec.option_getD.comp (Primrec.list_getElem?.comp hrow hu) (Primrec.const false)

private def rootTag (t : RelativeTerm Nat) : Nat := (t.code - 1).unpair.1
private def rootIndex (t : RelativeTerm Nat) : Nat := (t.code - 1).unpair.2.unpair.1
private def rootArgument (t : RelativeTerm Nat) : RelativeTerm Nat :=
  (decode (t.code - 1).unpair.2.unpair.2).getD (.parameter 0)

private theorem rootTag_primrec : Primrec rootTag :=
  Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.nat_sub.comp code_primrec (Primrec.const 1)))

private theorem rootIndex_primrec : Primrec rootIndex :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.nat_sub.comp code_primrec (Primrec.const 1)))))

private theorem rootArgument_primrec : Primrec rootArgument := by
  have harg := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.nat_sub.comp code_primrec (Primrec.const 1)))))
  exact Primrec.option_getD.comp (decode_primrec.comp harg) (Primrec.const (RelativeTerm.parameter 0))

/-- The constructor step of the original fuel recursion, with an arbitrary
    finite previous-answer function. -/
def advance (cmp : RelativeTerm Nat → RelativeTerm Nat → Bool) :
    RelativeTerm Nat → RelativeTerm Nat → Bool
  | .theta k a, .theta l b =>
      if k < l then true else if l < k then false else
        (cmp a b && (exposedThetaList k a).all (fun q => cmp q (.theta l b))) ||
        (exposedThetaList k b).any (fun q => !cmp q (.theta k a))
  | t, u => lexLT cmp (thetaAtoms t) (thetaAtoms u)

def tableStep (table : Matrix) (t u : RelativeTerm Nat) : Bool :=
  let k := rootIndex t
  let l := rootIndex u
  let a := rootArgument t
  let b := rootArgument u
  cond ((rootTag t == 2) && (rootTag u == 2))
    (cond (decide (k < l)) true (cond (decide (l < k)) false
      ((lookup table a b && (exposedThetaList k a).all (fun q => lookup table q u)) ||
        (exposedThetaList k b).any (fun q => !lookup table q t))))
    (lexLT (lookup table) (thetaAtoms t) (thetaAtoms u))

theorem tableStep_eq (table : Matrix) (t u : RelativeTerm Nat) :
    tableStep table t u = advance (lookup table) t u := by
  cases t <;> cases u <;>
    simp [tableStep, advance, rootTag, rootIndex, rootArgument, code, Nat.unpair_pair]

theorem tableStep_primrec : Primrec (fun p : Matrix × (RelativeTerm Nat × RelativeTerm Nat) =>
    tableStep p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Matrix × (RelativeTerm Nat × RelativeTerm Nat) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hu : Primrec (fun p : Matrix × (RelativeTerm Nat × RelativeTerm Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hk := rootIndex_primrec.comp ht
  have hl := rootIndex_primrec.comp hu
  have ha := rootArgument_primrec.comp ht
  have hb := rootArgument_primrec.comp hu
  have hab := lookup_primrec.comp (Primrec.fst.pair (ha.pair hb))
  have hall : Primrec (fun p : Matrix × (RelativeTerm Nat × RelativeTerm Nat) =>
      (exposedThetaList (rootIndex p.2.1) (rootArgument p.2.1)).all
        (fun q => lookup p.1 q p.2.2)) := by
    have htest : Primrec₂ (fun p : Matrix × (RelativeTerm Nat × RelativeTerm Nat) =>
        fun q : RelativeTerm Nat => lookup p.1 q p.2.2) :=
      (lookup_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        (Primrec.snd.pair (hu.comp Primrec.fst)))).to₂
    exact (listAll_primrec _ htest).comp Primrec.id (exposedThetaList_primrec.comp hk ha)
  have hany : Primrec (fun p : Matrix × (RelativeTerm Nat × RelativeTerm Nat) =>
      (exposedThetaList (rootIndex p.2.1) (rootArgument p.2.2)).any
        (fun q => !lookup p.1 q p.2.1)) := by
    have htest : Primrec₂ (fun p : Matrix × (RelativeTerm Nat × RelativeTerm Nat) =>
        fun q : RelativeTerm Nat => !lookup p.1 q p.2.1) :=
      (Primrec.not.comp (lookup_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        (Primrec.snd.pair (ht.comp Primrec.fst))))).to₂
    exact (listAny_primrec _ htest).comp Primrec.id (exposedThetaList_primrec.comp hk hb)
  have hlex := (lexLT_primrec (.parameter 0) lookup lookup_primrec).comp
    (Primrec.fst.pair ((thetaAtoms_primrec.comp ht).pair (thetaAtoms_primrec.comp hu)))
  have htag := Primrec.and.comp
    (Primrec.beq.comp (rootTag_primrec.comp ht) (Primrec.const 2))
    (Primrec.beq.comp (rootTag_primrec.comp hu) (Primrec.const 2))
  exact htag.cond ((Primrec.nat_lt.comp hk hl).decide.cond (Primrec.const true)
    ((Primrec.nat_lt.comp hl hk).decide.cond (Primrec.const false)
      (Primrec.or.comp (Primrec.and.comp hab hall) hany))) hlex

private theorem advance_congr (bound : Nat) (t u : RelativeTerm Nat)
    (f g : RelativeTerm Nat → RelativeTerm Nat → Bool)
    (ht : t.code < bound) (hu : u.code < bound)
    (h : ∀ x y : RelativeTerm Nat, x.code < bound → y.code < bound → f x y = g x y) :
    advance f t u = advance g t u := by
  have hlex (x y : RelativeTerm Nat) (hx : x.code < bound) (hy : y.code < bound) :
      lexLT f (thetaAtoms x) (thetaAtoms y) = lexLT g (thetaAtoms x) (thetaAtoms y) := by
    apply lex_congr_on
    intro a ha b hb
    have hac := (thetaAtoms_code_le x a ha).trans_lt hx
    have hbc := (thetaAtoms_code_le y b hb).trans_lt hy
    exact ⟨h a b hac hbc, h b a hbc hac⟩
  cases t with
  | parameter p => exact hlex _ _ ht hu
  | sum a b => exact hlex _ _ ht hu
  | theta k a =>
    cases u with
    | parameter p => exact hlex _ _ ht hu
    | sum b c => exact hlex _ _ ht hu
    | theta l b =>
      have ha := (theta_argument_code_lt k a).trans ht
      have hb := (theta_argument_code_lt l b).trans hu
      have hall : (exposedThetaList k a).all (fun q => f q (.theta l b)) =
          (exposedThetaList k a).all (fun q => g q (.theta l b)) := by
        apply all_congr_on
        intro q hq
        exact h q _ ((exposedThetaList_code_le k a q hq).trans_lt ha) hu
      have hany : (exposedThetaList k b).any (fun q => !f q (.theta k a)) =
          (exposedThetaList k b).any (fun q => !g q (.theta k a)) := by
        apply any_congr_on
        intro q hq
        rw [h q _ ((exposedThetaList_code_le k b q hq).trans_lt hb) ht]
      simp only [advance, h a b ha hb, hall, hany]

private def rawTree (c : Nat) : RelativeTerm Nat := (decode c).getD (.parameter 0)

private theorem rawTree_primrec : Primrec rawTree :=
  Primrec.option_getD.comp decode_primrec (Primrec.const (RelativeTerm.parameter 0))

private def zeroMatrix (bound : Nat) : Matrix :=
  (List.range bound).map (fun _ => (List.range bound).map (fun _ => false))

private def matrixStep (bound : Nat) (previous : Matrix) : Matrix :=
  (List.range bound).map (fun x => (List.range bound).map
    (fun y => tableStep previous (rawTree x) (rawTree y)))

private theorem zeroMatrix_primrec : Primrec zeroMatrix := by
  have hr : Primrec₂ (fun b : Nat => fun _ : Nat => (List.range b).map (fun _ => false)) :=
    (Primrec.list_map (Primrec.list_range.comp Primrec.fst) (Primrec.const false).to₂).to₂
  exact Primrec.list_map Primrec.list_range hr

private theorem matrixStep_primrec : Primrec₂ matrixStep := by
  have hrows : Primrec (fun p : Nat × Matrix => List.range p.1) :=
    Primrec.list_range.comp Primrec.fst
  have hrow : Primrec₂ (fun p : Nat × Matrix => fun x : Nat =>
      (List.range p.1).map (fun y => tableStep p.2 (rawTree x) (rawTree y))) := by
    have hlist : Primrec (fun p : (Nat × Matrix) × Nat => List.range p.1.1) :=
      Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)
    have hcell : Primrec₂ (fun p : (Nat × Matrix) × Nat => fun y : Nat =>
        tableStep p.1.2 (rawTree p.2) (rawTree y)) := by
      have hprevious : Primrec (fun p : ((Nat × Matrix) × Nat) × Nat => p.1.1.2) :=
        Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
      have hx : Primrec (fun p : ((Nat × Matrix) × Nat) × Nat => rawTree p.1.2) :=
        rawTree_primrec.comp (Primrec.snd.comp Primrec.fst)
      have hy : Primrec (fun p : ((Nat × Matrix) × Nat) × Nat => rawTree p.2) :=
        rawTree_primrec.comp Primrec.snd
      exact (tableStep_primrec.comp (hprevious.pair (hx.pair hy))).to₂
    exact (Primrec.list_map hlist hcell).to₂
  exact (Primrec.list_map hrows hrow).to₂

/-- Ordinary primitive recursion in fuel, with a fixed finite square bound. -/
def matrix (bound fuel : Nat) : Matrix :=
  Nat.rec (zeroMatrix bound) (fun _ previous => matrixStep bound previous) fuel

theorem matrix_primrec : Primrec₂ matrix :=
  Primrec.nat_rec zeroMatrix_primrec
    ((matrixStep_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂)

private theorem lookup_zero (bound : Nat) (t u : RelativeTerm Nat)
    (ht : t.code < bound) (hu : u.code < bound) : lookup (zeroMatrix bound) t u = false := by
  simp [lookup, zeroMatrix, List.getElem?_range ht, List.getElem?_range hu,
    List.getElem?_replicate, ht, hu]

private theorem lookup_step (bound : Nat) (previous : Matrix) (t u : RelativeTerm Nat)
    (ht : t.code < bound) (hu : u.code < bound) :
    lookup (matrixStep bound previous) t u = tableStep previous t u := by
  simp [lookup, matrixStep, rawTree, List.getElem?_range ht, List.getElem?_range hu]

/-- Correctness holds for every fuel and every actual tree in the square,
    independently of admissibility, normality and semantic denotation. -/
theorem matrix_correct (bound fuel : Nat) (t u : RelativeTerm Nat)
    (ht : t.code < bound) (hu : u.code < bound) :
    lookup (matrix bound fuel) t u = lessFuel fuel t u := by
  induction fuel generalizing t u with
  | zero => exact lookup_zero bound t u ht hu
  | succ fuel ih =>
    change lookup (matrixStep bound (matrix bound fuel)) t u = _
    rw [lookup_step bound _ t u ht hu, tableStep_eq,
      advance_congr bound t u (lookup (matrix bound fuel)) (lessFuel fuel) ht hu
        (fun x y hx hy => ih x y hx hy)]
    cases t <;> cases u <;> rfl

theorem lessFuel_primrec : Primrec (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) =>
    lessFuel p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) => p.2.1.code) :=
    code_primrec.comp (Primrec.fst.comp Primrec.snd)
  have hu : Primrec (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) => p.2.2.code) :=
    code_primrec.comp (Primrec.snd.comp Primrec.snd)
  have hb := Primrec.succ.comp (Primrec.nat_max.comp ht hu)
  have hmatrix := matrix_primrec.comp hb Primrec.fst
  have h := lookup_primrec.comp (hmatrix.pair Primrec.snd)
  have heq : (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) =>
      lookup (matrix (max p.2.1.code p.2.2.code + 1) p.1) p.2.1 p.2.2) =
      (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) => lessFuel p.1 p.2.1 p.2.2) := by
    funext p
    exact matrix_correct _ _ _ _ (Nat.lt_succ_of_le (le_max_left _ _))
      (Nat.lt_succ_of_le (le_max_right _ _))
  rw [heq] at h
  exact h

theorem less_primrec : Primrec₂ less := by
  have hf := Primrec.nat_add.comp (size_primrec.comp Primrec.fst) (size_primrec.comp Primrec.snd)
  exact (lessFuel_primrec.comp (hf.pair Primrec.id)).to₂

theorem equal_primrec : Primrec₂ equal := by
  have hreverse := less_primrec.comp Primrec.snd Primrec.fst
  exact (Primrec.and.comp (Primrec.not.comp less_primrec) (Primrec.not.comp hreverse)).to₂

private def rawCompare (cmp : RelativeTerm Nat → RelativeTerm Nat → Bool) (c d : Nat) : Bool :=
  ((decode c).isSome && (decode d).isSome) && cmp (rawTree c) (rawTree d)

private theorem rawCompare_primrec (cmp : RelativeTerm Nat → RelativeTerm Nat → Bool)
    (hc : Primrec₂ cmp) : Primrec₂ (rawCompare cmp) := by
  have hleft : Primrec (fun p : Nat × Nat => (decode p.1).isSome) :=
    Primrec.option_isSome.comp (decode_primrec.comp Primrec.fst)
  have hright : Primrec (fun p : Nat × Nat => (decode p.2).isSome) :=
    Primrec.option_isSome.comp (decode_primrec.comp Primrec.snd)
  exact (Primrec.and.comp (Primrec.and.comp hleft hright)
    (hc.comp (rawTree_primrec.comp Primrec.fst) (rawTree_primrec.comp Primrec.snd))).to₂

theorem lessCode_primrec : Primrec₂ lessCode := by
  have heq : rawCompare less = lessCode := by
    funext c d
    cases hc : decode c <;> cases hd : decode d <;>
      simp [rawCompare, rawTree, lessCode, hc, hd]
  rw [← heq]
  exact rawCompare_primrec less less_primrec

theorem equalCode_primrec : Primrec₂ equalCode := by
  have heq : rawCompare equal = equalCode := by
    funext c d
    cases hc : decode c <;> cases hd : decode d <;>
      simp [rawCompare, rawTree, equalCode, hc, hd]
  rw [← heq]
  exact rawCompare_primrec equal equal_primrec

end Alexander313.Wilken.RelativeTerm.SourceOne.Comparison.Effective
