import Alexander313.Effective.RecordedGuardPrograms
import Alexander313.Effective.RecordedConsequencePrograms
import Alexander313.RecordedMarkers
import Alexander313.ShapeCoding

/-!
# Literal marker formation and exact finite freshness tests

Tags are arbitrary natural numbers. Freshness inspects the whole source shape
and every nested shape, while distinctness checks the actual tag list. The
marker formulas, order and holder-local indexed heads are unchanged.
-/

noncomputable section

namespace Alexander313
namespace Formula

theorem markerTag_primrec : Primrec (markerTag Nat) := by
  have h := Primrec.nat_rec₁ (Formula.imp Formula.falsum Formula.falsum)
    (Formula.imp_primrec.comp (Primrec.const Formula.falsum) Primrec.snd).to₂
  exact h.of_eq (by intro n; induction n <;> simp_all [markerTag])

/-- The code list visits the current shape before its children. -/
def subshapeCodes : Formula Nat → List Nat
  | φ@(.falsum) => [φ.shape.code]
  | φ@(.equal _ _) => [φ.shape.code]
  | φ@(.imp ψ χ) => φ.shape.code :: (subshapeCodes ψ ++ subshapeCodes χ)
  | φ@(.conj ψ χ) => φ.shape.code :: (subshapeCodes ψ ++ subshapeCodes χ)
  | φ@(.disj ψ χ) => φ.shape.code :: (subshapeCodes ψ ++ subshapeCodes χ)
  | φ@(.neg ψ) => φ.shape.code :: subshapeCodes ψ
  | φ@(.all _ ψ) => φ.shape.code :: subshapeCodes ψ
  | φ@(.ex _ ψ) => φ.shape.code :: subshapeCodes ψ
  | φ@(.know _ ψ) => φ.shape.code :: subshapeCodes ψ

@[simp] theorem mem_subshapeCodes (φ : Formula Nat) (sh : Shape Nat) :
    sh.code ∈ subshapeCodes φ ↔ sh ∈ φ.shape.subshapes := by
  induction φ <;> simp_all [subshapeCodes, Shape.subshapes, Formula.shape]

/-- Explicit raw course recursion, including the current source shape. -/
def subshapeCodesCode : Nat → List Nat
  | 0 => []
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    shapeCode (k + 1) ::
      cond ((tag == 2) || (tag == 3) || (tag == 4))
        (subshapeCodesCode p.unpair.1 ++ subshapeCodesCode p.unpair.2)
        (cond (tag == 5) (subshapeCodesCode p)
          (cond ((tag == 6) || (tag == 7) || (tag == 8))
            (subshapeCodesCode p.unpair.2) []))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def subshapeStep (h : List (List Nat)) : List Nat :=
  let k := h.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (h.length == 0) []
    (shapeCode h.length ::
      cond ((tag == 2) || (tag == 3) || (tag == 4))
        ((h[p.unpair.1]?.getD []) ++ (h[p.unpair.2]?.getD []))
        (cond (tag == 5) (h[p]?.getD [])
          (cond ((tag == 6) || (tag == 7) || (tag == 8))
            (h[p.unpair.2]?.getD []) [])))

private theorem subshapeStep_primrec : Primrec subshapeStep := by
  have hk := Primrec.nat_sub.comp
    (Primrec.list_length : Primrec (fun h : List (List Nat) => h.length)) (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have get (f : List (List Nat) → Nat) (hf : Primrec f) :
      Primrec (fun h : List (List Nat) => h[f h]?.getD []) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hf) (Primrec.const [])
  exact (Primrec.beq.comp Primrec.list_length (Primrec.const 0)).cond (Primrec.const [])
    (Primrec.list_cons.comp (shapeCode_primrec.comp Primrec.list_length)
      ((Primrec.or.comp (Primrec.or.comp (test 2) (test 3)) (test 4)).cond
        (Primrec.list_append.comp (get _ hl) (get _ hr))
        ((test 5).cond (get _ hp)
          ((Primrec.or.comp (Primrec.or.comp (test 6) (test 7)) (test 8)).cond
            (get _ hr) (Primrec.const [])))))

theorem subshapeCodesCode_primrec : Primrec subshapeCodesCode := by
  have hg : Primrec₂ (fun (_ : Unit) (h : List (List Nat)) => some (subshapeStep h)) :=
    ((Primrec.option_some.comp subshapeStep_primrec).comp Primrec.snd).to₂
  have htable := Primrec.nat_strong_rec (fun (_ : Unit) n => subshapeCodesCode n) hg
    (by
      intro a n
      cases n with
      | zero => simp [subshapeStep, subshapeCodesCode]
      | succ k =>
        have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
        have hl : k.unpair.2.unpair.1 < k + 1 :=
          lt_of_le_of_lt (Nat.unpair_left_le _) hp
        have hr : k.unpair.2.unpair.2 < k + 1 :=
          lt_of_le_of_lt (Nat.unpair_right_le _) hp
        simp [subshapeStep, subshapeCodesCode, hp, hl, hr])
  exact htable.comp (Primrec.const ()) Primrec.id

@[simp] theorem subshapeCodesCode_code (φ : Formula Nat) :
    subshapeCodesCode (φ.code id) = subshapeCodes φ := by
  induction φ <;>
    simp_all [subshapeCodesCode, subshapeCodes, Formula.code, Formula.shapeCode,
      Formula.shape, Shape.code, EncodedSyntax.node, Nat.unpair_pair]

end Formula
namespace RecordedFormula

theorem markerTag_primrec : Primrec (markerTag Head) := by
  have h := Primrec.nat_rec₁ (Formula.imp Formula.falsum Formula.falsum : Syntax)
    (imp_primrec.comp (Primrec.const Formula.falsum) Primrec.snd).to₂
  exact h.of_eq (by intro n; induction n <;> simp_all [markerTag])

theorem markerFormulas_primrec :
    Primrec₂ (markerFormulas (Label := Nat)) := by
  have hstep : Primrec₂ (fun (p : Nat × List (Nat × Nat)) (q : Nat × Nat) =>
      Formula.know (RecordedHead.indexed p.1 q.1) (markerTag Head q.2)) :=
    (know_primrec.comp
      (RecordedHead.indexed_primrec.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (markerTag_primrec.comp (Primrec.snd.comp Primrec.snd))).to₂
  exact (Primrec.list_map Primrec.snd hstep).to₂

theorem markerPadding_primrec :
    Primrec (fun p : (Nat × List (Nat × Nat)) × Syntax => markerPadding p.1.1 p.1.2 p.2) :=
  chain_primrec.comp (markerFormulas_primrec.comp
    (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)) Primrec.snd

end RecordedFormula
namespace RecordedMarkerProgram

open RecordedFormula RecordedGuardProgram

def points (ms : List (Nat × Nat)) : List Nat := ms.map Prod.fst
def tags (ms : List (Nat × Nat)) : List Nat := ms.map Prod.snd

theorem points_primrec : Primrec points :=
  Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd).to₂

theorem tags_primrec : Primrec tags :=
  Primrec.list_map Primrec.id (Primrec.snd.comp Primrec.snd).to₂

@[simp] theorem points_toFinset (ms : List (Nat × Nat)) :
    (points ms).toFinset = markerPoints ms := rfl

def markerDistinctCheck (ms : List (Nat × Nat)) : Bool :=
  allCheck (fun p : Nat × Nat => decide (p.1 ≠ p.2)) (forwardPairs (tags ms))

theorem markerDistinctCheck_primrec : Primrec markerDistinctCheck := by
  have ht : Primrec₂ (fun (_ : Unit) (p : Nat × Nat) => decide (p.1 ≠ p.2)) :=
    ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).not.decide).to₂
  exact (allCheck_primrec _ ht).comp (Primrec.const ())
    (forwardPairs_primrec.comp tags_primrec)

theorem markerDistinctCheck_iff (ms : List (Nat × Nat)) :
    markerDistinctCheck ms = true ↔ (ms.map Prod.snd).Nodup := by
  rw [markerDistinctCheck, allCheck_iff]
  have h := forwardPairs_exact (fun x y : Nat => x ≠ y) (tags ms)
  simpa only [tags, decide_eq_true_eq, List.nodup_iff_pairwise_ne] using h

def freshAt (σ : Formula Nat) (p : Nat × Nat) : Bool :=
  !listMember (Formula.subshapeCodesCode (σ.code id))
    (Formula.shapeCode ((markerTag Nat p.2).code id))

theorem freshAt_primrec : Primrec₂ freshAt := by
  exact (Primrec.not.comp (listMember_primrec.comp
    (Formula.subshapeCodesCode_primrec.comp (Formula.code_primrec.comp Primrec.fst))
    (Formula.shapeCode_primrec.comp (Formula.code_primrec.comp
      (Formula.markerTag_primrec.comp (Primrec.snd.comp Primrec.snd)))))).to₂

@[simp] theorem freshAt_iff (σ : Formula Nat) (p : Nat × Nat) :
    freshAt σ p = true ↔ (markerTag Nat p.2).shape ∉ σ.shape.subshapes := by
  simp [freshAt, listMember]

def markerFreshCheck (σ : Formula Nat) (ms : List (Nat × Nat)) : Bool := allCheck (freshAt σ) ms

theorem markerFreshCheck_primrec : Primrec₂ markerFreshCheck := allCheck_primrec _ freshAt_primrec

theorem markerFreshCheck_iff (σ : Formula Nat) (ms : List (Nat × Nat)) :
    markerFreshCheck σ ms = true ↔ ∀ p ∈ ms, (markerTag Nat p.2).shape ∉ σ.shape.subshapes := by
  simp only [markerFreshCheck, allCheck_iff, freshAt_iff]

end RecordedMarkerProgram
end Alexander313
