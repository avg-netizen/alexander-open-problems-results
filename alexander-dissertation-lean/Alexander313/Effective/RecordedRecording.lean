import Alexander313.Effective.RecordedAdmissibility
import Alexander313.Effective.RecordedFiniteMasks
import Alexander313.ShapeCoding

/-!
# Actual source-shape recording from shared finite tables

The course table constructs the literal recorded tree. Its head operation
uses the original source argument's shape code, before any recording below
that head. Arithmetic payloads, quantified variable names and all original
program numerals stay fixed. The finite instance uses the same mask and
first-match label table at every occurrence, with natural label default zero.
No effectivity premise is needed for that actual finite instance.
-/

noncomputable section

namespace Alexander313
namespace RecordedFormula

section Uniform

variable {α : Type} [Primcodable α]

def recordCode (head : α → Nat → Nat → Head) (a : α) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond ((tag == 0) || (tag == 1)) (k + 1)
      (cond ((tag == 2) || (tag == 3) || (tag == 4))
        (EncodedSyntax.node tag
          (Nat.pair (recordCode head a p.unpair.1) (recordCode head a p.unpair.2)))
        (cond (tag == 5) (EncodedSyntax.node 5 (recordCode head a p))
          (cond ((tag == 6) || (tag == 7))
            (EncodedSyntax.node tag (Nat.pair p.unpair.1 (recordCode head a p.unpair.2)))
            (cond (tag == 8)
              (EncodedSyntax.node 8
                (Nat.pair (head a p.unpair.1 (Formula.shapeCode p.unpair.2)).code
                  (recordCode head a p.unpair.2))) 0))))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def recordingStep (head : α → Nat → Nat → Head) (a : α)
    (history : List Nat) : Nat :=
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
              (EncodedSyntax.node 8
                (Nat.pair (head a p.unpair.1 (Formula.shapeCode p.unpair.2)).code
                  (history[p.unpair.2]?.getD 0))) 0)))))

private theorem recordingStep_primrec (head : α → Nat → Nat → Head)
    (hh : Primrec (fun p : α × (Nat × Nat) => head p.1 p.2.1 p.2.2)) :
    Primrec₂ (recordingStep head) := by
  have hn : Primrec (fun p : α × List Nat => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have get (f : α × List Nat → Nat) (hf : Primrec f) :
      Primrec (fun p : α × List Nat => p.2[f p]?.getD 0) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hf) (Primrec.const 0)
  have hhead := RecordedHead.code_primrec.comp
    (hh.comp (Primrec.pair Primrec.fst
      (Primrec.pair hl (Formula.shapeCode_primrec.comp hr))))
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const 0)
    ((Primrec.or.comp (test 0) (test 1)).cond hn
      ((Primrec.or.comp (Primrec.or.comp (test 2) (test 3)) (test 4)).cond
        (EncodedSyntax.node_primrec.comp ht (Primrec₂.natPair.comp (get _ hl) (get _ hr)))
        ((test 5).cond (EncodedSyntax.node_primrec.comp (Primrec.const 5) (get _ hp))
          ((Primrec.or.comp (test 6) (test 7)).cond
            (EncodedSyntax.node_primrec.comp ht (Primrec₂.natPair.comp hl (get _ hr)))
            ((test 8).cond
              (EncodedSyntax.node_primrec.comp (Primrec.const 8)
                (Primrec₂.natPair.comp hhead (get _ hr))) (Primrec.const 0))))))).to₂

theorem recordCode_primrec (head : α → Nat → Nat → Head)
    (hh : Primrec (fun p : α × (Nat × Nat) => head p.1 p.2.1 p.2.2)) :
    Primrec₂ (recordCode head) := by
  have hg := Primrec.option_some.comp₂ (recordingStep_primrec head hh)
  exact Primrec.nat_strong_rec (recordCode head) hg (by
    intro a n
    cases n with
    | zero => simp [recordingStep, recordCode]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [recordingStep, recordCode, hp, hl, hr])

@[simp] theorem recordCode_code (head : α → Nat → Nat → Head) (a : α)
    (φ : Formula Nat) :
    recordCode head a (φ.code id) =
      (φ.record (fun b sh => head a b sh.code)).code RecordedHead.code := by
  induction φ <;>
    simp_all [recordCode, Formula.code, Formula.record, EncodedSyntax.node, Nat.unpair_pair]

def record (head : α → Nat → Nat → Head) (a : α) (φ : Formula Nat) : Syntax :=
  φ.record (fun b sh => head a b sh.code)

theorem record_primrec (head : α → Nat → Nat → Head)
    (hh : Primrec (fun p : α × (Nat × Nat) => head p.1 p.2.1 p.2.2)) :
    Primrec₂ (record head) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, record, recordCode_code] using
    (recordCode_primrec head hh).comp Primrec.fst (Formula.code_primrec.comp Primrec.snd)

end Uniform

end RecordedFormula

namespace RecordedTable

theorem lookup_primrec {Label : Type} [Primcodable Label] (default : Label) :
    Primrec₂ (lookup default) := by
  have step : Primrec₂ (fun (p : List (Nat × Label) × Nat)
      (s : (Nat × Label) × Label) => if s.1.1 = p.2 then s.1.2 else s.2) :=
    (Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.fst (Primrec.const default) step).to₂

end RecordedTable

namespace RecordedFormula

abbrev FiniteRecordData := (List Nat × List Nat) × (RecordedTable.Mask × List (Nat × Nat))

def finiteHead (p : FiniteRecordData) (a shape : Nat) : Head :=
  cond (listMember p.1.2 a)
    (cond (listMember (RecordedTable.maskKeys p.2.1) (Nat.pair a shape))
      (.live a) (.ghost a))
    (cond (listMember p.1.1 a)
      (.indexed a (RecordedTable.lookup 0 p.2.2 (Nat.pair a shape))) (.live a))

theorem finiteHead_primrec :
    Primrec (fun p : FiniteRecordData × (Nat × Nat) => finiteHead p.1 p.2.1 p.2.2) := by
  have hA : Primrec (fun p : FiniteRecordData × (Nat × Nat) => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hE : Primrec (fun p : FiniteRecordData × (Nat × Nat) => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hM : Primrec (fun p : FiniteRecordData × (Nat × Nat) => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hT : Primrec (fun p : FiniteRecordData × (Nat × Nat) => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have ha : Primrec (fun p : FiniteRecordData × (Nat × Nat) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hshape : Primrec (fun p : FiniteRecordData × (Nat × Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hkey := Primrec₂.natPair.comp ha hshape
  have hlive := RecordedHead.live_primrec.comp ha
  have hghost := RecordedHead.ghost_primrec.comp ha
  have hindexed := RecordedHead.indexed_primrec.comp ha
    ((RecordedTable.lookup_primrec 0).comp hT hkey)
  exact (listMember_primrec.comp hE ha).cond
    ((listMember_primrec.comp (RecordedTable.maskKeys_primrec.comp hM) hkey).cond hlive hghost)
    ((listMember_primrec.comp hA ha).cond hindexed hlive)

@[simp] theorem finiteHead_shape (p : FiniteRecordData) (a : Nat) (sh : Shape Nat) :
    finiteHead p a sh.code =
      RecordedTable.heads p.1.1.toFinset p.1.2.toFinset p.2.1 0 p.2.2 a sh := by
  by_cases he : a ∈ p.1.2 <;>
    by_cases hm : (a, sh) ∈ RecordedTable.mask p.2.1 <;>
    by_cases ha : a ∈ p.1.1 <;>
    simp [finiteHead, listMember, RecordedTable.heads, mainHeads, maskedHeads,
      RecordedTable.queryKey, RecordedTable.mem_maskKeys, he, hm, ha]

@[simp] theorem finiteHead_erase (p : FiniteRecordData) (a shape : Nat) :
    (finiteHead p a shape).erase = a := by
  cases he : listMember p.1.2 a <;>
    cases hm : listMember (RecordedTable.maskKeys p.2.1) (Nat.pair a shape) <;>
    cases ha : listMember p.1.1 a <;>
    simp [finiteHead, he, hm, ha, RecordedHead.erase]

def finiteRecord (p : FiniteRecordData) (φ : Formula Nat) : Syntax :=
  φ.record (RecordedTable.heads p.1.1.toFinset p.1.2.toFinset p.2.1 0 p.2.2)

theorem finiteRecord_eq_record (p : FiniteRecordData) (φ : Formula Nat) :
    record finiteHead p φ = finiteRecord p φ := by
  unfold record finiteRecord
  congr 1
  funext a sh
  exact finiteHead_shape p a sh

theorem finiteRecord_primrec : Primrec₂ finiteRecord :=
  (record_primrec finiteHead finiteHead_primrec).of_eq finiteRecord_eq_record

def finiteRecordCode (p : FiniteRecordData) (n : Nat) : Nat := recordCode finiteHead p n

theorem finiteRecordCode_primrec : Primrec₂ finiteRecordCode :=
  recordCode_primrec finiteHead finiteHead_primrec

@[simp] theorem finiteRecordCode_code (p : FiniteRecordData) (φ : Formula Nat) :
    finiteRecordCode p (φ.code id) = (finiteRecord p φ).code RecordedHead.code := by
  rw [finiteRecordCode, recordCode_code]
  change (record finiteHead p φ).code RecordedHead.code = _
  rw [finiteRecord_eq_record]

@[simp] theorem finiteRecord_erase (p : FiniteRecordData) (φ : Formula Nat) :
    (finiteRecord p φ).erase = φ := by
  apply Formula.erase_record
  exact mainHeads_erase _ _ _ _

end RecordedFormula
end Alexander313
