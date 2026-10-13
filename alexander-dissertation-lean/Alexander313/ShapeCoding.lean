import Alexander313.Effective.FormulaSyntax
import Alexander313.Effective.FormulaSubstitution

/-!
# Literal skeleton codes and primitive-recursive extraction

Arithmetic leaves and bound variable names are erased; modal owner names
and the complete logical/modal tree are retained. Thus a finite protected
skeleton table can be checked without decoding a formula by classical
choice and without mistaking numeral substitution for a new skeleton.
-/

namespace Alexander313
namespace Shape

def code : Shape Nat → Nat
  | .falsum => EncodedSyntax.node 0 0
  | .equal => EncodedSyntax.node 1 0
  | .imp φ ψ => EncodedSyntax.node 2 (Nat.pair φ.code ψ.code)
  | .conj φ ψ => EncodedSyntax.node 3 (Nat.pair φ.code ψ.code)
  | .disj φ ψ => EncodedSyntax.node 4 (Nat.pair φ.code ψ.code)
  | .neg φ => EncodedSyntax.node 5 φ.code
  | .all φ => EncodedSyntax.node 6 φ.code
  | .ex φ => EncodedSyntax.node 7 φ.code
  | .know a φ => EncodedSyntax.node 8 (Nat.pair a φ.code)

theorem code_injective : Function.Injective code := by
  intro φ ψ h
  induction φ generalizing ψ <;> cases ψ <;>
    simp_all [code, EncodedSyntax.node, Nat.pair_eq_pair] <;> aesop

@[simp] theorem code_eq_iff (φ ψ : Shape Nat) : φ.code = ψ.code ↔ φ = ψ :=
  code_injective.eq_iff

end Shape
namespace Formula

def shapeCode : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond ((tag == 0) || (tag == 1)) (EncodedSyntax.node tag 0)
      (cond ((tag == 2) || (tag == 3) || (tag == 4))
        (EncodedSyntax.node tag (Nat.pair (shapeCode p.unpair.1) (shapeCode p.unpair.2)))
        (cond (tag == 5) (EncodedSyntax.node 5 (shapeCode p))
          (cond ((tag == 6) || (tag == 7)) (EncodedSyntax.node tag (shapeCode p.unpair.2))
            (cond (tag == 8)
              (EncodedSyntax.node 8 (Nat.pair p.unpair.1 (shapeCode p.unpair.2))) 0))))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def shapeStep (history : List Nat) : Nat :=
  let k := history.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (history.length == 0) 0
    (cond ((tag == 0) || (tag == 1)) (EncodedSyntax.node tag 0)
      (cond ((tag == 2) || (tag == 3) || (tag == 4))
        (EncodedSyntax.node tag
          (Nat.pair (history[p.unpair.1]?.getD 0) (history[p.unpair.2]?.getD 0)))
        (cond (tag == 5) (EncodedSyntax.node 5 (history[p]?.getD 0))
          (cond ((tag == 6) || (tag == 7))
            (EncodedSyntax.node tag (history[p.unpair.2]?.getD 0))
            (cond (tag == 8) (EncodedSyntax.node 8
              (Nat.pair p.unpair.1 (history[p.unpair.2]?.getD 0))) 0)))))

private theorem shapeStep_primrec : Primrec shapeStep := by
  have hk : Primrec (fun h : List Nat => h.length - 1) :=
    Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have get (f : List Nat → Nat) (hf : Primrec f) :
      Primrec (fun h : List Nat => h[f h]?.getD 0) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hf) (Primrec.const 0)
  have node (t p : List Nat → Nat) (ht : Primrec t) (hp : Primrec p) :=
    EncodedSyntax.node_primrec.comp ht hp
  exact (Primrec.beq.comp Primrec.list_length (Primrec.const 0)).cond (Primrec.const 0)
    ((Primrec.or.comp (test 0) (test 1)).cond (node _ _ ht (Primrec.const 0))
      ((Primrec.or.comp (Primrec.or.comp (test 2) (test 3)) (test 4)).cond
        (node _ _ ht (Primrec₂.natPair.comp (get _ hl) (get _ hr)))
        ((test 5).cond (node _ _ (Primrec.const 5) (get _ hp))
          ((Primrec.or.comp (test 6) (test 7)).cond (node _ _ ht (get _ hr))
            ((test 8).cond (node _ _ (Primrec.const 8)
              (Primrec₂.natPair.comp hl (get _ hr))) (Primrec.const 0))))))

theorem shapeCode_primrec : Primrec shapeCode := by
  have hg : Primrec₂ (fun (_ : Unit) (h : List Nat) => some (shapeStep h)) :=
    ((Primrec.option_some.comp shapeStep_primrec).comp Primrec.snd).to₂
  have htable := Primrec.nat_strong_rec (fun (_ : Unit) n => shapeCode n) hg
    (by
      intro a n
      cases n with
      | zero => simp [shapeStep, shapeCode]
      | succ k =>
        have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
        have hl : k.unpair.2.unpair.1 < k + 1 :=
          lt_of_le_of_lt (Nat.unpair_left_le _) hp
        have hr : k.unpair.2.unpair.2 < k + 1 :=
          lt_of_le_of_lt (Nat.unpair_right_le _) hp
        simp [shapeStep, shapeCode, hp, hl, hr])
  exact htable.comp (Primrec.const ()) Primrec.id

@[simp] theorem shapeCode_code (φ : Formula Nat) :
    shapeCode (φ.code id) = φ.shape.code := by
  induction φ <;>
    simp_all [shapeCode, code, shape, Shape.code, EncodedSyntax.node, Nat.unpair_pair]

end Formula

noncomputable def shapeTable (H : Finset (Nat × Shape Nat)) : List Nat :=
  H.toList.map (fun p => Nat.pair p.1 p.2.code)

@[simp] theorem mem_shapeTable (H : Finset (Nat × Shape Nat)) (a : Nat)
    (φ : Shape Nat) : Nat.pair a φ.code ∈ shapeTable H ↔ (a, φ) ∈ H := by
  simp only [shapeTable, List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨⟨b, ψ⟩, hp, heq⟩
    have h := Nat.pair_eq_pair.mp heq
    have hψ := Shape.code_injective h.2
    have hb : b = a := h.1
    change ψ = φ at hψ
    subst b
    subst ψ
    exact hp
  · intro h
    exact ⟨(a, φ), h, rfl⟩

end Alexander313
