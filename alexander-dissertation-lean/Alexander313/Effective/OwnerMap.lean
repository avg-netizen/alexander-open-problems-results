import Alexander313.Effective.SyntaxFilter
import Alexander313.Effective.FormulaSubstitution
import Alexander313.Alexander.ModelTransport

/-!
# Primitive-recursive owner maps and actual reduct recognizers

Modal owner names are transformed in the existing literal formula encoding.
Variable names, terms, quantifiers and every program numeral remain fixed.
The resulting recognizer is an actual partial-recursive program, filtered for
original syntax. No effective map or recursive-enumerability premise is added.
-/

namespace Alexander313
namespace Formula

def mapOwnerCode (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond ((tag == 0) || (tag == 1)) (k + 1)
      (cond ((tag == 2) || (tag == 3) || (tag == 4))
        (EncodedSyntax.node tag
          (Nat.pair (mapOwnerCode f p.unpair.1) (mapOwnerCode f p.unpair.2)))
        (cond (tag == 5) (EncodedSyntax.node 5 (mapOwnerCode f p))
          (cond ((tag == 6) || (tag == 7))
            (EncodedSyntax.node tag (Nat.pair p.unpair.1 (mapOwnerCode f p.unpair.2)))
            (cond (tag == 8)
              (EncodedSyntax.node 8 (Nat.pair (f p.unpair.1)
                (mapOwnerCode f p.unpair.2))) 0))))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def ownerMapStep (f : Nat → Nat) (history : List Nat) : Nat :=
  let k := history.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (history.length == 0) 0
    (cond ((tag == 0) || (tag == 1)) history.length
      (cond ((tag == 2) || (tag == 3) || (tag == 4))
        (EncodedSyntax.node tag
          (Nat.pair (history[p.unpair.1]?.getD 0) (history[p.unpair.2]?.getD 0)))
        (cond (tag == 5) (EncodedSyntax.node 5 (history[p]?.getD 0))
          (cond ((tag == 6) || (tag == 7))
            (EncodedSyntax.node tag (Nat.pair p.unpair.1 (history[p.unpair.2]?.getD 0)))
            (cond (tag == 8)
              (EncodedSyntax.node 8 (Nat.pair (f p.unpair.1)
                (history[p.unpair.2]?.getD 0))) 0)))))

private theorem ownerMapStep_primrec (f : Nat → Nat) (hf : Primrec f) :
    Primrec (ownerMapStep f) := by
  have hk : Primrec (fun h : List Nat => h.length - 1) :=
    Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have get (u : List Nat → Nat) (hu : Primrec u) :
      Primrec (fun h : List Nat => h[u h]?.getD 0) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hu) (Primrec.const 0)
  have binary := Primrec₂.natPair.comp (get _ hl) (get _ hr)
  exact (Primrec.beq.comp Primrec.list_length (Primrec.const 0)).cond (Primrec.const 0)
    ((Primrec.or.comp (test 0) (test 1)).cond Primrec.list_length
      ((Primrec.or.comp (Primrec.or.comp (test 2) (test 3)) (test 4)).cond
        (EncodedSyntax.node_primrec.comp ht binary)
        ((test 5).cond (EncodedSyntax.node_primrec.comp (Primrec.const 5) (get _ hp))
          ((Primrec.or.comp (test 6) (test 7)).cond
            (EncodedSyntax.node_primrec.comp ht (Primrec₂.natPair.comp hl (get _ hr)))
            ((test 8).cond
              (EncodedSyntax.node_primrec.comp (Primrec.const 8)
                (Primrec₂.natPair.comp (hf.comp hl) (get _ hr)))
              (Primrec.const 0))))))

theorem mapOwnerCode_primrec (f : Nat → Nat) (hf : Primrec f) :
    Primrec (mapOwnerCode f) := by
  have hg : Primrec₂ (fun (_ : Unit) (h : List Nat) => some (ownerMapStep f h)) :=
    ((Primrec.option_some.comp (ownerMapStep_primrec f hf)).comp Primrec.snd).to₂
  have htable := Primrec.nat_strong_rec (fun (_ : Unit) n => mapOwnerCode f n) hg
    (by
      intro a n
      cases n with
      | zero => simp [ownerMapStep, mapOwnerCode]
      | succ k =>
        have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
        have hl : k.unpair.2.unpair.1 < k + 1 :=
          lt_of_le_of_lt (Nat.unpair_left_le _) hp
        have hr : k.unpair.2.unpair.2 < k + 1 :=
          lt_of_le_of_lt (Nat.unpair_right_le _) hp
        simp [ownerMapStep, mapOwnerCode, hp, hl, hr])
  exact htable.comp (Primrec.const ()) Primrec.id

@[simp] theorem mapOwnerCode_code (f : Nat → Nat) (φ : Formula Nat) :
    mapOwnerCode f (φ.code id) = (φ.mapOwner f).code id := by
  induction φ <;>
    simp_all [mapOwnerCode, code, mapOwner, EncodedSyntax.node, Nat.unpair_pair]

end Formula

def ownerMappedEvaluation (F : EffectiveFamily Nat) (f : Nat → Nat) (n : Nat) : Part Nat :=
  F.recognizes.eval
    (Nat.pair (f n.unpair.1) (Formula.mapOwnerCode f n.unpair.2))

theorem ownerMappedEvaluation_partrec (F : EffectiveFamily Nat)
    (f : Nat → Nat) (hf : Primrec f) : Partrec (ownerMappedEvaluation F f) := by
  have hi : Primrec (fun n : Nat => f n.unpair.1) :=
    hf.comp (Primrec.fst.comp Primrec.unpair)
  have hφ : Primrec (fun n : Nat => Formula.mapOwnerCode f n.unpair.2) :=
    (Formula.mapOwnerCode_primrec f hf).comp (Primrec.snd.comp Primrec.unpair)
  exact (Nat.Partrec.Code.eval_part.comp (Computable.const F.recognizes)
    (Primrec₂.natPair.comp hi hφ).to_comp)

theorem EffectiveFamily.ownerMapped_exists (F : EffectiveFamily Nat)
    (howners : ∀ i, F.encodeOwner i = i) (f : Nat → Nat) (hf : Primrec f) :
    ∃ G : EffectiveFamily Nat, (∀ i, G.encodeOwner i = i) ∧
      ∀ i φ, G.proves i φ ↔ F.proves (f i) (φ.mapOwner f) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (ownerMappedEvaluation_partrec F f hf))
  obtain ⟨G, hG, hcanonical⟩ := effectiveFamily_from_program c
  refine ⟨G, hcanonical, ?_⟩
  intro i φ
  rw [hG]
  change (c.eval (Nat.pair i (φ.code id))).Dom ↔ _
  rw [hc]
  simp only [ownerMappedEvaluation, Nat.unpair_pair, Formula.mapOwnerCode_code]
  have hownerFunction : F.encodeOwner = id := funext howners
  have hformula : F.encodeFormula (φ.mapOwner f) = (φ.mapOwner f).code id := by
    rw [F.formula_coding, hownerFunction]
  simpa only [howners, hformula, Program.domain] using
    F.recognizes_correct (f i) (φ.mapOwner f)

end Alexander313
