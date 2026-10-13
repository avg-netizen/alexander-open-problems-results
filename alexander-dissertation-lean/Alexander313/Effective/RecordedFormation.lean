import Alexander313.Effective.RecordedAdmissibility
import Alexander313.Effective.SchemaGenerators

/-!
# Literal recorded contexts and background formula formation

A context is represented by a finite list of actual frames. Every frame
constructs an existing one-hole context, and every existing context has such
a representative. The arithmetic row uses the full PA table, including
unrestricted modal induction, followed by the proved owner retraction.
-/

noncomputable section

namespace Alexander313
namespace RecordedFormula

abbrev Frame := (Nat × Nat) × Syntax

def frame (w : Frame) (c : Formula.Context Head) : Formula.Context Head :=
  if w.1.1 = 0 then .impLeft c w.2 else
  if w.1.1 = 1 then .impRight w.2 c else
  if w.1.1 = 2 then .conjLeft c w.2 else
  if w.1.1 = 3 then .conjRight w.2 c else
  if w.1.1 = 4 then .disjLeft c w.2 else
  if w.1.1 = 5 then .disjRight w.2 c else
  if w.1.1 = 6 then .neg c else
  if w.1.1 = 7 then .all w.1.2 c else
  if w.1.1 = 8 then .ex w.1.2 c else .know (RecordedHead.ofCode w.1.2) c

def frameFill (w : Frame) (φ : Syntax) : Syntax :=
  if w.1.1 = 0 then .imp φ w.2 else
  if w.1.1 = 1 then .imp w.2 φ else
  if w.1.1 = 2 then .conj φ w.2 else
  if w.1.1 = 3 then .conj w.2 φ else
  if w.1.1 = 4 then .disj φ w.2 else
  if w.1.1 = 5 then .disj w.2 φ else
  if w.1.1 = 6 then .neg φ else
  if w.1.1 = 7 then .all w.1.2 φ else
  if w.1.1 = 8 then .ex w.1.2 φ else .know (RecordedHead.ofCode w.1.2) φ

@[simp] theorem frame_fill (w : Frame) (c : Formula.Context Head) (φ : Syntax) :
    (frame w c).fill φ = frameFill w (c.fill φ) := by
  unfold frame frameFill
  split_ifs <;> rfl

theorem frameFill_primrec : Primrec₂ frameFill := by
  have ht : Primrec (fun p : Frame × Syntax => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hx : Primrec (fun p : Frame × Syntax => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hs : Primrec (fun p : Frame × Syntax => p.1.2) := Primrec.snd.comp Primrec.fst
  have test (n : Nat) := Primrec.eq.comp ht (Primrec.const n)
  exact (Primrec.ite (test 0) (imp_primrec.comp Primrec.snd hs)
    (Primrec.ite (test 1) (imp_primrec.comp hs Primrec.snd)
      (Primrec.ite (test 2) (conj_primrec.comp Primrec.snd hs)
        (Primrec.ite (test 3) (conj_primrec.comp hs Primrec.snd)
          (Primrec.ite (test 4) (disj_primrec.comp Primrec.snd hs)
            (Primrec.ite (test 5) (disj_primrec.comp hs Primrec.snd)
              (Primrec.ite (test 6) (neg_primrec.comp Primrec.snd)
                (Primrec.ite (test 7) (all_primrec.comp hx Primrec.snd)
                  (Primrec.ite (test 8) (ex_primrec.comp hx Primrec.snd)
                    (know_primrec.comp (RecordedHead.ofCode_primrec.comp hx) Primrec.snd)))))))))).to₂

def context (L : List Frame) : Formula.Context Head := L.foldr frame .hole
def contextFill (L : List Frame) (φ : Syntax) : Syntax := L.foldr frameFill φ

@[simp] theorem context_fill (L : List Frame) (φ : Syntax) :
    (context L).fill φ = contextFill L φ := by
  induction L <;> simp_all [context, contextFill, Formula.Context.fill]

theorem contextFill_primrec : Primrec₂ contextFill :=
  (Primrec.list_foldr Primrec.fst Primrec.snd
    (frameFill_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).to₂

theorem context_represents (c : Formula.Context Head) : ∃ L : List Frame, context L = c := by
  induction c with
  | hole => exact ⟨[], rfl⟩
  | impLeft c ψ ih => obtain ⟨L, rfl⟩ := ih; exact ⟨((0, 0), ψ) :: L, rfl⟩
  | impRight ψ c ih => obtain ⟨L, rfl⟩ := ih; exact ⟨((1, 0), ψ) :: L, rfl⟩
  | conjLeft c ψ ih => obtain ⟨L, rfl⟩ := ih; exact ⟨((2, 0), ψ) :: L, rfl⟩
  | conjRight ψ c ih => obtain ⟨L, rfl⟩ := ih; exact ⟨((3, 0), ψ) :: L, rfl⟩
  | disjLeft c ψ ih => obtain ⟨L, rfl⟩ := ih; exact ⟨((4, 0), ψ) :: L, rfl⟩
  | disjRight ψ c ih => obtain ⟨L, rfl⟩ := ih; exact ⟨((5, 0), ψ) :: L, rfl⟩
  | neg c ih => obtain ⟨L, rfl⟩ := ih; exact ⟨((6, 0), .falsum) :: L, rfl⟩
  | all x c ih => obtain ⟨L, rfl⟩ := ih; exact ⟨((7, x), .falsum) :: L, rfl⟩
  | ex x c ih => obtain ⟨L, rfl⟩ := ih; exact ⟨((8, x), .falsum) :: L, rfl⟩
  | know a c ih =>
    obtain ⟨L, rfl⟩ := ih
    exact ⟨((9, a.code), .falsum) :: L, by simp [context, frame]⟩

def collapse (L : List Frame) (b μ ν : Nat) (φ : Syntax) : Syntax :=
  Formula.contextualCollapse (context L) b μ ν φ

theorem collapse_primrec : Primrec (fun p : (List Frame × (Nat × (Nat × Nat))) × Syntax =>
    collapse p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) := by
  have hL : Primrec (fun p : (List Frame × (Nat × (Nat × Nat))) × Syntax => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun p : (List Frame × (Nat × (Nat × Nat))) × Syntax => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hμ : Primrec (fun p : (List Frame × (Nat × (Nat × Nat))) × Syntax => p.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hν : Primrec (fun p : (List Frame × (Nat × (Nat × Nat))) × Syntax => p.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hleft := contextFill_primrec.comp hL
    (know_primrec.comp (RecordedHead.indexed_primrec.comp hb hμ) Primrec.snd)
  have hright := contextFill_primrec.comp hL
    (know_primrec.comp (RecordedHead.indexed_primrec.comp hb hν) Primrec.snd)
  simpa only [collapse, Formula.contextualCollapse, context_fill] using
    universalClosure_primrec.comp (iff_primrec.comp hleft hright)

theorem indexedDeduction_primrec : Primrec (fun p : (Nat × Nat) × (Syntax × Syntax) =>
    Formula.indexedDeduction p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hh : Primrec (fun p : (Nat × Nat) × (Syntax × Syntax) =>
      RecordedHead.indexed p.1.1 p.1.2) :=
    RecordedHead.indexed_primrec.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst)
  have hφ : Primrec (fun p : (Nat × Nat) × (Syntax × Syntax) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hψ : Primrec (fun p : (Nat × Nat) × (Syntax × Syntax) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact universalClosure_primrec.comp (imp_primrec.comp
    (know_primrec.comp hh (imp_primrec.comp hφ hψ))
    (imp_primrec.comp (know_primrec.comp hh hφ) (know_primrec.comp hh hψ)))

theorem indexedIntrospection_primrec : Primrec (fun p : (Nat × (Nat × Nat)) × Syntax =>
    Formula.indexedIntrospection p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have ha : Primrec (fun p : (Nat × (Nat × Nat)) × Syntax => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hμ : Primrec (fun p : (Nat × (Nat × Nat)) × Syntax => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hν : Primrec (fun p : (Nat × (Nat × Nat)) × Syntax => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hk := know_primrec.comp (RecordedHead.indexed_primrec.comp ha hμ) Primrec.snd
  exact universalClosure_primrec.comp
    (imp_primrec.comp hk (know_primrec.comp (RecordedHead.indexed_primrec.comp ha hν) hk))

def paFormula (w : SyntacticBackground.Witness) : Syntax := decode (SyntacticBackground.formula 0 w)

theorem paFormula_primrec : Primrec paFormula :=
  decode_primrec.comp (SyntacticBackground.formula_primrec.comp (Primrec.const 0) Primrec.id)

theorem paFormula_closed (w : SyntacticBackground.Witness) : (paFormula w).Closed := by
  have h := SyntacticBackground.admits_closed (SyntacticBackground.formula_admitted 0 w)
  simpa only [paFormula, decode, Formula.Closed, Formula.freeVars_mapOwner] using h

theorem paFormula_pa (w : SyntacticBackground.Witness) (htag : w.1.1 ≤ 6) :
    PAInstance Head (paFormula w) := by
  have hp : PAInstance Nat (SyntacticBackground.formula 0 w) := by
    unfold SyntacticBackground.formula
    split_ifs
    · exact .successor_ne_zero
    · exact .successor_injective
    · exact .add_zero
    · exact .add_succ
    · exact .mul_zero
    · exact .mul_succ
    · exact .induction w.2.1 w.1.2
    all_goals omega
  exact hp.mapOwner RecordedHead.ofCode

private theorem source_pa_witness (σ : Formula Nat) (h : PAInstance Nat σ) :
    ∃ w : SyntacticBackground.Witness, w.1.1 ≤ 6 ∧ σ = SyntacticBackground.formula 0 w := by
  cases h with
  | successor_ne_zero => exact ⟨((0, 0), (.falsum, .falsum)), by decide, rfl⟩
  | successor_injective => exact ⟨((1, 0), (.falsum, .falsum)), by decide, rfl⟩
  | add_zero => exact ⟨((2, 0), (.falsum, .falsum)), by decide, rfl⟩
  | add_succ => exact ⟨((3, 0), (.falsum, .falsum)), by decide, rfl⟩
  | mul_zero => exact ⟨((4, 0), (.falsum, .falsum)), by decide, rfl⟩
  | mul_succ => exact ⟨((5, 0), (.falsum, .falsum)), by decide, rfl⟩
  | induction φ x => exact ⟨((6, x), (φ, .falsum)), Nat.le_refl 6, rfl⟩

theorem pa_represents (σ : Syntax) (h : PAInstance Head σ) :
    ∃ w : SyntacticBackground.Witness, w.1.1 ≤ 6 ∧ σ = paFormula w := by
  obtain ⟨w, ht, hw⟩ := source_pa_witness (encode σ) (h.mapOwner RecordedHead.code)
  exact ⟨w, ht, by simpa only [decode_encode, paFormula] using congrArg decode hw⟩

def «prefix» (a : Nat) (L : List Nat) (φ : Syntax) : Syntax :=
  L.foldr (fun ν ψ => Formula.know (.indexed a ν) ψ) φ

theorem prefix_primrec : Primrec (fun p : (Nat × List Nat) × Syntax => «prefix» p.1.1 p.1.2 p.2) :=
  Primrec.list_foldr (Primrec.snd.comp Primrec.fst) Primrec.snd
    (know_primrec.comp (RecordedHead.indexed_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

theorem prefix_closed (a : Nat) (L : List Nat) (φ : Syntax) (h : φ.Closed) :
    («prefix» a L φ).Closed := by
  induction L <;> simp_all [«prefix», Formula.Closed, Formula.freeVars]

end RecordedFormula
end Alexander313
