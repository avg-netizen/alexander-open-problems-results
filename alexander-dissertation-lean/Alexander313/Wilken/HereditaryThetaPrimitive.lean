import Alexander313.Wilken.HereditaryThetaComparison

/-! # Uniform primitive recursion for the actual hereditary comparator

At each fuel step, the table stores the actual previous comparison answers
for every level and every pair of literal codes in a finite square. Parameter
queries open an earlier level; opened atoms, theta arguments and exposed nodes
remain inside the square. Correctness is an all-raw-tree equality with the
literal fuel algorithm. Admission and normality are not premises of its PR
proof. Ordinal correctness keeps the original source hypotheses. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Theta.Effective

open ThetaCourse
open SourceOne.Comparison (lexLT)
open SourceOne.Comparison.Effective

abbrev Table := List (List (List Bool))
abbrev Configuration := Nat × Nat

def lookup (table : Table) (r : Nat) (t u : RelativeTerm Nat) : Bool :=
  (((table[r]?.getD [])[t.code]?.getD [])[u.code]?).getD false

theorem lookup_primrec : Primrec
    (fun p : Table × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      lookup p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hr : Primrec (fun p : Table × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : Table × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      p.2.2.1.code) := code_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hu : Primrec (fun p : Table × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      p.2.2.2.code) := code_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hlevel := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp Primrec.fst hr) (Primrec.const ([] : List (List Bool)))
  have hrow := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp hlevel ht) (Primrec.const ([] : List Bool))
  exact Primrec.option_getD.comp (Primrec.list_getElem?.comp hrow hu) (Primrec.const false)

private def rootTag (t : RelativeTerm Nat) : Nat := (t.code - 1).unpair.1
private def rootPayload (t : RelativeTerm Nat) : Nat := (t.code - 1).unpair.2
private def rootIndex (t : RelativeTerm Nat) : Nat := (rootPayload t).unpair.1
private def rootArgument (t : RelativeTerm Nat) : RelativeTerm Nat := rawTree (rootPayload t).unpair.2

private theorem rootTag_primrec : Primrec rootTag :=
  Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.nat_sub.comp code_primrec (Primrec.const 1)))

private theorem rootPayload_primrec : Primrec rootPayload :=
  Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.nat_sub.comp code_primrec (Primrec.const 1)))

private theorem rootIndex_primrec : Primrec rootIndex :=
  Primrec.fst.comp (Primrec.unpair.comp rootPayload_primrec)

private theorem rootArgument_primrec : Primrec rootArgument :=
  rawTree_primrec.comp (Primrec.snd.comp (Primrec.unpair.comp rootPayload_primrec))

/-- One literal fuel step using the finite previous-answer function. -/
def advance (cmp : Nat → RelativeTerm Nat → RelativeTerm Nat → Bool) (r : Nat) :
    RelativeTerm Nat → RelativeTerm Nat → Bool
  | .parameter p, .parameter q =>
      cond (r == 0) false (cmp (r - 1) (rawTree p) (rawTree q))
  | .parameter _, .theta _ _ => true
  | .theta _ _, .parameter _ => false
  | .theta k a, .theta l b =>
      if k < l then true else if l < k then false else
        (cmp r a b && (exposedThetaList k a).all (fun q => cmp r q (.theta l b))) ||
        (exposedThetaList k b).any (fun q => !cmp r q (.theta k a))
  | t, u => lexLT (cmp r) (atoms r t) (atoms r u)

def tableStep (table : Table) (r : Nat) (t u : RelativeTerm Nat) : Bool :=
  let k := rootIndex t
  let l := rootIndex u
  let a := rootArgument t
  let b := rootArgument u
  cond ((rootTag t == 0) && (rootTag u == 0))
    (cond (r == 0) false
      (lookup table (r - 1) (rawTree (rootPayload t)) (rawTree (rootPayload u))))
    (cond ((rootTag t == 0) && (rootTag u == 2)) true
      (cond ((rootTag t == 2) && (rootTag u == 0)) false
        (cond ((rootTag t == 2) && (rootTag u == 2))
          (cond (decide (k < l)) true (cond (decide (l < k)) false
            ((lookup table r a b &&
              (exposedThetaList k a).all (fun q => lookup table r q u)) ||
              (exposedThetaList k b).any (fun q => !lookup table r q t))))
          (lexLT (lookup table r) (atoms r t) (atoms r u)))))

theorem tableStep_eq (table : Table) (r : Nat) (t u : RelativeTerm Nat) :
    tableStep table r t u = advance (lookup table) r t u := by
  cases t <;> cases u <;>
    simp [tableStep, advance, rootTag, rootPayload, rootIndex, rootArgument, code,
      Nat.unpair_pair, rawTree]

theorem tableStep_primrec : Primrec
    (fun p : Table × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      tableStep p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hr : Primrec (fun p : Table × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : Table × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hu : Primrec (fun p : Table × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hk := rootIndex_primrec.comp ht
  have hl := rootIndex_primrec.comp hu
  have ha := rootArgument_primrec.comp ht
  have hb := rootArgument_primrec.comp hu
  have htagT := rootTag_primrec.comp ht
  have htagU := rootTag_primrec.comp hu
  have tag (i j : Nat) := Primrec.and.comp (Primrec.beq.comp htagT (Primrec.const i))
    (Primrec.beq.comp htagU (Primrec.const j))
  have hab := lookup_primrec.comp (Primrec.fst.pair (hr.pair (ha.pair hb)))
  have hparameters := lookup_primrec.comp (Primrec.fst.pair
    ((Primrec.nat_sub.comp hr (Primrec.const 1)).pair
      ((rawTree_primrec.comp (rootPayload_primrec.comp ht)).pair
        (rawTree_primrec.comp (rootPayload_primrec.comp hu)))))
  have hall : Primrec
      (fun p : Table × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
        (exposedThetaList (rootIndex p.2.2.1) (rootArgument p.2.2.1)).all
          (fun q => lookup p.1 p.2.1 q p.2.2.2)) := by
    have htest : Primrec₂
        (fun p : Table × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
          fun q : RelativeTerm Nat => lookup p.1 p.2.1 q p.2.2.2) :=
      (lookup_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        ((hr.comp Primrec.fst).pair (Primrec.snd.pair (hu.comp Primrec.fst))))).to₂
    exact (listAll_primrec _ htest).comp Primrec.id (exposedThetaList_primrec.comp hk ha)
  have hany : Primrec
      (fun p : Table × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
        (exposedThetaList (rootIndex p.2.2.1) (rootArgument p.2.2.2)).any
          (fun q => !lookup p.1 p.2.1 q p.2.2.1)) := by
    have htest : Primrec₂
        (fun p : Table × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
          fun q : RelativeTerm Nat => !lookup p.1 p.2.1 q p.2.2.1) :=
      (Primrec.not.comp (lookup_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        ((hr.comp Primrec.fst).pair (Primrec.snd.pair (ht.comp Primrec.fst)))))).to₂
    exact (listAny_primrec _ htest).comp Primrec.id (exposedThetaList_primrec.comp hk hb)
  have hcmp : Primrec
      (fun p : (Table × Nat) × (RelativeTerm Nat × RelativeTerm Nat) =>
        lookup p.1.1 p.1.2 p.2.1 p.2.2) :=
    lookup_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have hlex := (lexLT_primrec (.parameter 0) (fun d => lookup d.1 d.2) hcmp).comp
    ((Primrec.fst.pair hr).pair
      ((atoms_primrec.comp hr ht).pair (atoms_primrec.comp hr hu)))
  exact (tag 0 0).cond ((Primrec.beq.comp hr (Primrec.const 0)).cond
    (Primrec.const false) hparameters)
    ((tag 0 2).cond (Primrec.const true) ((tag 2 0).cond (Primrec.const false)
      ((tag 2 2).cond ((Primrec.nat_lt.comp hk hl).decide.cond (Primrec.const true)
        ((Primrec.nat_lt.comp hl hk).decide.cond (Primrec.const false)
          (Primrec.or.comp (Primrec.and.comp hab hall) hany))) hlex)))

private theorem advance_congr (R bound r : Nat) (t u : RelativeTerm Nat)
    (f g : Nat → RelativeTerm Nat → RelativeTerm Nat → Bool)
    (hr : r ≤ R) (ht : t.code < bound) (hu : u.code < bound)
    (h : ∀ s x y, s ≤ R → x.code < bound → y.code < bound → f s x y = g s x y) :
    advance f r t u = advance g r t u := by
  have hlex (x y : RelativeTerm Nat) (hx : x.code < bound) (hy : y.code < bound) :
      lexLT (f r) (atoms r x) (atoms r y) = lexLT (g r) (atoms r x) (atoms r y) := by
    apply lex_congr_on
    intro a ha b hb
    have hac := (atoms_code_le r x a ha).trans_lt hx
    have hbc := (atoms_code_le r y b hb).trans_lt hy
    exact ⟨h r a b hr hac hbc, h r b a hr hbc hac⟩
  cases t with
  | parameter p =>
    cases u with
    | parameter q =>
      have hp := (parameter_payload_code_le p).trans_lt ht
      have hq := (parameter_payload_code_le q).trans_lt hu
      simp only [advance, h (r - 1) _ _ ((Nat.sub_le r 1).trans hr) hp hq]
    | sum a b => exact hlex _ _ ht hu
    | theta k a => rfl
  | sum a b => exact hlex _ _ ht hu
  | theta k a =>
    cases u with
    | parameter p => rfl
    | sum b c => exact hlex _ _ ht hu
    | theta l b =>
      have ha := (theta_argument_code_lt k a).trans ht
      have hb := (theta_argument_code_lt l b).trans hu
      have hall : (exposedThetaList k a).all (fun q => f r q (.theta l b)) =
          (exposedThetaList k a).all (fun q => g r q (.theta l b)) := by
        apply all_congr_on
        intro q hq
        exact h r q _ hr ((exposedThetaList_code_le k a q hq).trans_lt ha) hu
      have hany : (exposedThetaList k b).any (fun q => !f r q (.theta k a)) =
          (exposedThetaList k b).any (fun q => !g r q (.theta k a)) := by
        apply any_congr_on
        intro q hq
        rw [h r q _ hr ((exposedThetaList_code_le k b q hq).trans_lt hb) ht]
      simp only [advance, h r a b hr ha hb, hall, hany]

private def zeroSquare (bound : Nat) : List (List Bool) :=
  (List.range bound).map (fun _ => (List.range bound).map (fun _ => false))

private def zeroTable (cfg : Configuration) : Table :=
  (List.range (cfg.1 + 1)).map (fun _ => zeroSquare cfg.2)

private def squareStep (d : Table × Nat) (bound : Nat) : List (List Bool) :=
  (List.range bound).map (fun x => (List.range bound).map
    (fun y => tableStep d.1 d.2 (rawTree x) (rawTree y)))

private def tableAdvance (cfg : Configuration) (previous : Table) : Table :=
  (List.range (cfg.1 + 1)).map (fun r => squareStep (previous, r) cfg.2)

private theorem zeroSquare_primrec : Primrec zeroSquare := by
  have hrow : Primrec₂ (fun b : Nat => fun _ : Nat =>
      (List.range b).map (fun _ => false)) :=
    (Primrec.list_map (Primrec.list_range.comp Primrec.fst) (Primrec.const false).to₂).to₂
  exact Primrec.list_map Primrec.list_range hrow

private theorem zeroTable_primrec : Primrec zeroTable := by
  have hlevels : Primrec (fun cfg : Configuration => List.range (cfg.1 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)
  have hs : Primrec₂ (fun cfg : Configuration => fun _ : Nat => zeroSquare cfg.2) :=
    (zeroSquare_primrec.comp (Primrec.snd.comp Primrec.fst)).to₂
  exact Primrec.list_map hlevels hs

private theorem squareStep_primrec : Primrec₂ squareStep := by
  have hrows : Primrec (fun p : (Table × Nat) × Nat => List.range p.2) :=
    Primrec.list_range.comp Primrec.snd
  have hrow : Primrec₂ (fun p : (Table × Nat) × Nat => fun x : Nat =>
      (List.range p.2).map (fun y => tableStep p.1.1 p.1.2 (rawTree x) (rawTree y))) := by
    have hlist : Primrec (fun p : ((Table × Nat) × Nat) × Nat => List.range p.1.2) :=
      Primrec.list_range.comp (Primrec.snd.comp Primrec.fst)
    have hcell : Primrec₂ (fun p : ((Table × Nat) × Nat) × Nat => fun y : Nat =>
        tableStep p.1.1.1 p.1.1.2 (rawTree p.2) (rawTree y)) := by
      have hdata : Primrec (fun p : (((Table × Nat) × Nat) × Nat) × Nat =>
          p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
      have hprevious := Primrec.fst.comp hdata
      have hr := Primrec.snd.comp hdata
      have hx : Primrec (fun p : (((Table × Nat) × Nat) × Nat) × Nat =>
          rawTree p.1.2) := rawTree_primrec.comp (Primrec.snd.comp Primrec.fst)
      have hy : Primrec (fun p : (((Table × Nat) × Nat) × Nat) × Nat =>
          rawTree p.2) := rawTree_primrec.comp Primrec.snd
      exact (tableStep_primrec.comp (hprevious.pair (hr.pair (hx.pair hy)))).to₂
    exact (Primrec.list_map hlist hcell).to₂
  exact (Primrec.list_map hrows hrow).to₂

private theorem tableAdvance_primrec : Primrec₂ tableAdvance := by
  have hlevels : Primrec (fun p : Configuration × Table => List.range (p.1.1 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
  have hs : Primrec₂ (fun p : Configuration × Table => fun r : Nat =>
      squareStep (p.2, r) p.1.2) :=
    (squareStep_primrec.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).to₂
  exact (Primrec.list_map hlevels hs).to₂

def table (cfg : Configuration) (fuel : Nat) : Table :=
  Nat.rec (zeroTable cfg) (fun _ previous => tableAdvance cfg previous) fuel

theorem table_primrec : Primrec₂ table :=
  Primrec.nat_rec zeroTable_primrec
    ((tableAdvance_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂)

private theorem lookup_zero (cfg : Configuration) (r : Nat) (t u : RelativeTerm Nat)
    (hr : r ≤ cfg.1) (ht : t.code < cfg.2) (hu : u.code < cfg.2) :
    lookup (zeroTable cfg) r t u = false := by
  simp [lookup, zeroTable, zeroSquare, List.getElem?_range (Nat.lt_succ_of_le hr),
    List.getElem?_range ht, List.getElem?_range hu, List.getElem?_replicate,
    Nat.lt_succ_of_le hr, ht, hu]

private theorem lookup_step (cfg : Configuration) (previous : Table)
    (r : Nat) (t u : RelativeTerm Nat)
    (hr : r ≤ cfg.1) (ht : t.code < cfg.2) (hu : u.code < cfg.2) :
    lookup (tableAdvance cfg previous) r t u = tableStep previous r t u := by
  simp [lookup, tableAdvance, squareStep, List.getElem?_range (Nat.lt_succ_of_le hr),
    List.getElem?_range ht, List.getElem?_range hu]

/-- Equality with the literal fuel algorithm on all raw trees and all levels
    in the table, independently of admission and ordinal semantics. -/
theorem table_correct (cfg : Configuration) (fuel r : Nat) (t u : RelativeTerm Nat)
    (hr : r ≤ cfg.1) (ht : t.code < cfg.2) (hu : u.code < cfg.2) :
    lookup (table cfg fuel) r t u = lessFuel fuel r t u := by
  induction fuel generalizing r t u with
  | zero => exact lookup_zero cfg r t u hr ht hu
  | succ fuel ih =>
    change lookup (tableAdvance cfg (table cfg fuel)) r t u = _
    rw [lookup_step cfg _ r t u hr ht hu, tableStep_eq,
      advance_congr cfg.1 cfg.2 r t u (lookup (table cfg fuel)) (lessFuel fuel)
        hr ht hu (fun s x y hs hx hy => ih s x y hs hx hy)]
    cases t <;> cases u <;> cases r <;> rfl

theorem lessFuel_primrec : Primrec
    (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      lessFuel p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hr : Primrec (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      p.2.2.1.code) := code_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hu : Primrec (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      p.2.2.2.code) := code_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hbound := Primrec.succ.comp (Primrec.nat_max.comp ht hu)
  have htable := table_primrec.comp (hr.pair hbound) Primrec.fst
  have h := lookup_primrec.comp (htable.pair Primrec.snd)
  have heq : (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
      lookup (table (p.2.1, max p.2.2.1.code p.2.2.2.code + 1) p.1)
        p.2.1 p.2.2.1 p.2.2.2) =
      (fun p : Nat × (Nat × (RelativeTerm Nat × RelativeTerm Nat)) =>
        lessFuel p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    funext p
    exact table_correct _ _ _ _ _ le_rfl
      (Nat.lt_succ_of_le (le_max_left _ _)) (Nat.lt_succ_of_le (le_max_right _ _))
  rw [heq] at h
  exact h

theorem less_primrec : Primrec
    (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) => less p.1 p.2.1 p.2.2) := by
  have hf : Primrec (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) =>
      expandedSize p.1 p.2.1.code + expandedSize p.1 p.2.2.code) := Primrec.nat_add.comp
    (expandedSize_primrec.comp Primrec.fst (code_primrec.comp (Primrec.fst.comp Primrec.snd)))
    (expandedSize_primrec.comp Primrec.fst (code_primrec.comp (Primrec.snd.comp Primrec.snd)))
  exact lessFuel_primrec.comp (hf.pair Primrec.id)

theorem equal_primrec : Primrec
    (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) => equal p.1 p.2.1 p.2.2) := by
  have hreverse : Primrec (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) =>
      less p.1 p.2.2 p.2.1) := less_primrec.comp (Primrec.fst.pair
    ((Primrec.snd.comp Primrec.snd).pair (Primrec.fst.comp Primrec.snd)))
  exact Primrec.and.comp (Primrec.not.comp less_primrec) (Primrec.not.comp hreverse)

private def rawCompare (cmp : Nat → RelativeTerm Nat → RelativeTerm Nat → Bool)
    (r c d : Nat) : Bool :=
  ((decode c).isSome && (decode d).isSome) && cmp r (rawTree c) (rawTree d)

private theorem rawCompare_primrec (cmp : Nat → RelativeTerm Nat → RelativeTerm Nat → Bool)
    (hc : Primrec (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) => cmp p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Nat × (Nat × Nat) => rawCompare cmp p.1 p.2.1 p.2.2) := by
  have hl : Primrec (fun p : Nat × (Nat × Nat) => (decode p.2.1).isSome) :=
    Primrec.option_isSome.comp (decode_primrec.comp (Primrec.fst.comp Primrec.snd))
  have hr : Primrec (fun p : Nat × (Nat × Nat) => (decode p.2.2).isSome) :=
    Primrec.option_isSome.comp (decode_primrec.comp (Primrec.snd.comp Primrec.snd))
  have hcmp : Primrec (fun p : Nat × (Nat × Nat) => cmp p.1 (rawTree p.2.1) (rawTree p.2.2)) :=
    hc.comp (Primrec.fst.pair
    ((rawTree_primrec.comp (Primrec.fst.comp Primrec.snd)).pair
      (rawTree_primrec.comp (Primrec.snd.comp Primrec.snd))))
  exact Primrec.and.comp (Primrec.and.comp hl hr) hcmp

theorem lessCode_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => lessCode p.1 p.2.1 p.2.2) := by
  have heq : rawCompare less = lessCode := by
    funext r c d
    cases hc : decode c <;> cases hd : decode d <;>
      simp [rawCompare, rawTree, lessCode, hc, hd]
  rw [← heq]
  exact rawCompare_primrec less less_primrec

theorem equalCode_primrec : Primrec
    (fun p : Nat × (Nat × Nat) => equalCode p.1 p.2.1 p.2.2) := by
  have heq : rawCompare equal = equalCode := by
    funext r c d
    cases hc : decode c <;> cases hd : decode d <;>
      simp [rawCompare, rawTree, equalCode, hc, hd]
  rw [← heq]
  exact rawCompare_primrec equal equal_primrec

theorem less_computable : Computable
    (fun p : Nat × (RelativeTerm Nat × RelativeTerm Nat) => less p.1 p.2.1 p.2.2) :=
  less_primrec.to_comp

theorem lessCode_computable : Computable
    (fun p : Nat × (Nat × Nat) => lessCode p.1 p.2.1 p.2.2) := lessCode_primrec.to_comp

end Alexander313.Wilken.RelativeTerm.Hereditary.Theta.Effective
