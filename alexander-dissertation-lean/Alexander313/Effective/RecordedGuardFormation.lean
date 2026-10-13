import Alexander313.Effective.RecordedTreeFold
import Alexander313.RecordedGuardRequirements

/-!
# Actual primitive-recursive guard requirement extraction

These operations retain the literal recorded tree. Rank is the erased
argument's shape rank, not the tree code, largest label or number of modal
heads. Neither ghost nor indexed heads stop main inspection.
-/

noncomputable section

namespace Alexander313
namespace GuardRequirements

theorem append_primrec : Primrec₂ (append (Label := Nat)) :=
  ((Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂

end GuardRequirements
namespace RecordedFormula

def labelListHead (_ : Unit) (owner _body : Nat) (value : List Nat) : List Nat :=
  cond (owner.unpair.1 == 1) (owner.unpair.2.unpair.2 :: value) value

def labelListCode (n : Nat) : List Nat :=
  ValueFold.code (· ++ ·) id [] labelListHead () n

theorem labelListCode_primrec : Primrec labelListCode := by
  have ho : Primrec (fun p : Unit × (Nat × (Nat × List Nat)) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ht := Primrec.fst.comp (Primrec.unpair.comp ho)
  have hν := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp ho)))
  have hv : Primrec (fun p : Unit × (Nat × (Nat × List Nat)) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact (ValueFold.code_primrec _ _ _ _ Primrec.list_append Primrec.id
    ((Primrec.beq.comp ht (Primrec.const 1)).cond (Primrec.list_cons.comp hν hv) hv)).comp
      (Primrec.const ()) Primrec.id

@[simp] theorem labelListCode_code (φ : Syntax) :
    labelListCode (φ.code RecordedHead.code) = φ.labelList := by
  unfold labelListCode
  rw [ValueFold.code_formula]
  induction φ with
  | know a φ ih => cases a <;>
      simp_all [ValueFold.formula, labelListHead, Formula.labelList, RecordedHead.code,
        Nat.unpair_pair]
  | _ => simp_all [ValueFold.formula, Formula.labelList]

def rankHead (_ : Unit) (_owner _body : Nat) (value : Nat) : Nat := value + 1

def rankCode (n : Nat) : Nat :=
  ValueFold.code (fun x y => x + y + 1) (fun x => x + 1) 1 rankHead () n

theorem rankCode_primrec : Primrec rankCode := by
  have hc : Primrec₂ (fun x y : Nat => x + y + 1) :=
    (Primrec.succ.comp Primrec.nat_add).to₂
  have hh : Primrec (fun p : Unit × (Nat × (Nat × Nat)) =>
      rankHead p.1 p.2.1 p.2.2.1 p.2.2.2) :=
    Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (ValueFold.code_primrec _ _ _ _ hc Primrec.succ hh).comp (Primrec.const ()) Primrec.id

@[simp] theorem rankCode_code (φ : Syntax) :
    rankCode (φ.code RecordedHead.code) = φ.erase.shape.rank := by
  unfold rankCode
  rw [ValueFold.code_formula]
  induction φ <;> simp_all [ValueFold.formula, rankHead, Formula.erase, Formula.mapOwner,
    Formula.shape, Shape.rank]

def labelEdges (ν : Nat) (L : List Nat) : List (Nat × Nat) := L.map (fun μ => (μ, ν))

theorem labelEdges_primrec : Primrec₂ labelEdges :=
  (Primrec.list_map Primrec.snd
    ((Primrec.snd.pair (Primrec.fst.comp Primrec.fst)).to₂)).to₂

def indexedRequirementsHead (k owner body : Nat) (p : GuardRequirements Nat) :
    GuardRequirements Nat :=
  cond (owner.unpair.1 == 1)
    ((k, owner.unpair.2.unpair.2) :: p.1,
      labelEdges owner.unpair.2.unpair.2 (labelListCode body) ++ p.2) p

theorem indexedRequirementsHead_primrec :
    Primrec (fun p : Nat × (Nat × (Nat × GuardRequirements Nat)) =>
      indexedRequirementsHead p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have ho : Primrec (fun p : Nat × (Nat × (Nat × GuardRequirements Nat)) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ht := Primrec.fst.comp (Primrec.unpair.comp ho)
  have hν := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp ho)))
  have hb : Primrec (fun p : Nat × (Nat × (Nat × GuardRequirements Nat)) => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hv : Primrec (fun p : Nat × (Nat × (Nat × GuardRequirements Nat)) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact (Primrec.beq.comp ht (Primrec.const 1)).cond
    ((Primrec.list_cons.comp (Primrec.fst.pair hν) (Primrec.fst.comp hv)).pair
      (Primrec.list_append.comp (labelEdges_primrec.comp hν (labelListCode_primrec.comp hb))
        (Primrec.snd.comp hv))) hv

def indexedRequirementsCode (k n : Nat) : GuardRequirements Nat :=
  ValueFold.code GuardRequirements.append id ([], []) indexedRequirementsHead k n

theorem indexedRequirementsCode_primrec : Primrec₂ indexedRequirementsCode :=
  ValueFold.code_primrec _ _ _ _ GuardRequirements.append_primrec Primrec.id
    indexedRequirementsHead_primrec

@[simp] theorem indexedRequirementsCode_code (k : Nat) (φ : Syntax) :
    indexedRequirementsCode k (φ.code RecordedHead.code) = φ.indexedGuardRequirements k := by
  unfold indexedRequirementsCode
  rw [ValueFold.code_formula]
  induction φ with
  | know a φ ih => cases a <;>
      simp_all [ValueFold.formula, indexedRequirementsHead, Formula.indexedGuardRequirements,
        RecordedHead.code, labelEdges, Nat.unpair_pair]
  | _ => simp_all [ValueFold.formula, Formula.indexedGuardRequirements]

def mainRequirementsHead (E : List Nat) (owner body : Nat) (p : GuardRequirements Nat) :
    GuardRequirements Nat :=
  cond ((owner.unpair.1 == 0) && listMember E owner.unpair.2)
    (GuardRequirements.append (indexedRequirementsCode (rankCode body) body) p) p

theorem mainRequirementsHead_primrec :
    Primrec (fun p : List Nat × (Nat × (Nat × GuardRequirements Nat)) =>
      mainRequirementsHead p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have ho : Primrec (fun p : List Nat × (Nat × (Nat × GuardRequirements Nat)) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun p : List Nat × (Nat × (Nat × GuardRequirements Nat)) => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hv : Primrec (fun p : List Nat × (Nat × (Nat × GuardRequirements Nat)) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have htest := Primrec.and.comp
    (Primrec.beq.comp (Primrec.fst.comp (Primrec.unpair.comp ho)) (Primrec.const 0))
    (listMember_primrec.comp Primrec.fst (Primrec.snd.comp (Primrec.unpair.comp ho)))
  exact htest.cond
    (GuardRequirements.append_primrec.comp
      (indexedRequirementsCode_primrec.comp (rankCode_primrec.comp hb) hb) hv) hv

def mainRequirementsCode (E : List Nat) (n : Nat) : GuardRequirements Nat :=
  ValueFold.code GuardRequirements.append id ([], []) mainRequirementsHead E n

theorem mainRequirementsCode_primrec : Primrec₂ mainRequirementsCode :=
  ValueFold.code_primrec _ _ _ _ GuardRequirements.append_primrec Primrec.id
    mainRequirementsHead_primrec

@[simp] theorem mainRequirementsCode_code (E : List Nat) (φ : Syntax) :
    mainRequirementsCode E (φ.code RecordedHead.code) = φ.mainGuardRequirements E.toFinset := by
  unfold mainRequirementsCode
  rw [ValueFold.code_formula]
  induction φ with
  | know a φ ih =>
    cases a with
    | live e => by_cases he : e ∈ E <;>
        simp_all [ValueFold.formula, mainRequirementsHead, Formula.mainGuardRequirements,
          RecordedHead.code, listMember, Nat.unpair_pair]
    | ghost e =>
      simp_all [ValueFold.formula, mainRequirementsHead, Formula.mainGuardRequirements,
        RecordedHead.code, listMember, Nat.unpair_pair]
    | indexed a ν =>
      simp_all [ValueFold.formula, mainRequirementsHead, Formula.mainGuardRequirements,
        RecordedHead.code, listMember, Nat.unpair_pair]
  | _ => simp_all [ValueFold.formula, Formula.mainGuardRequirements]

theorem mainRequirementsCode_exact (R₁ R₂ : Nat → Nat → Prop) (E B : List Nat) (φ : Syntax) :
    GuardRequirements.Holds R₁ R₂ B.toFinset (mainRequirementsCode E (φ.code RecordedHead.code)) ↔
      φ.MainGuarded R₁ R₂ E.toFinset B.toFinset := by
  rw [mainRequirementsCode_code, Formula.mainGuardRequirements_exact]

end RecordedFormula
end Alexander313
