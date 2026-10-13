import Alexander313.Alexander.NativeFormulaFormation
import Alexander313.Alexander.FirstOrderCalculus

/-!
# Actual native sentence labels

The numerical no-free-variable test is primitive recursive. Closed Nat-variable
formulas retract syntactically onto Empty-variable formulas; the retraction is
proved by induction, not by a semantic equivalence assumption. This constructs
the native sentence coding needed by the finite Hilbert checker.
-/

namespace Alexander313.Delta

private theorem biUnion_empty_iff {m : Nat} (f : Fin m → Finset Nat) :
    (Finset.univ.biUnion f = ∅) ↔ ∀ i, f i = ∅ := by
  constructor
  · intro h i
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    exact Finset.notMem_empty x (h ▸ Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
  · intro h
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact Finset.notMem_empty x (h i ▸ hi)

namespace NativeTerm

def noFreeCode : Nat → Bool
  | 0 => false
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) (p.unpair.1 == 1)
      (cond (tag == 1) true
        (cond (tag == 2) (noFreeCode p)
          (cond ((tag == 3) || (tag == 4))
            (noFreeCode p.unpair.1 && noFreeCode p.unpair.2) false)))
termination_by c => c
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def noFreeStep (h : List Bool) : Bool :=
  let k := h.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (h.length == 0) false
    (cond (tag == 0) (p.unpair.1 == 1)
      (cond (tag == 1) true
        (cond (tag == 2) (h[p]?.getD false)
          (cond ((tag == 3) || (tag == 4))
            (h[p.unpair.1]?.getD false && h[p.unpair.2]?.getD false) false))))

private theorem noFreeStep_primrec : Primrec noFreeStep := by
  have hk : Primrec (fun h : List Bool => h.length - 1) :=
    Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have get (f : List Bool → Nat) (hf : Primrec f) :
      Primrec (fun h : List Bool => h[f h]?.getD false) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hf)
      (Primrec.const false)
  exact (Primrec.beq.comp Primrec.list_length (Primrec.const 0)).cond (Primrec.const false)
    ((test 0).cond (Primrec.beq.comp (Primrec.fst.comp (Primrec.unpair.comp hp))
      (Primrec.const 1))
      ((test 1).cond (Primrec.const true)
        ((test 2).cond (get _ hp)
          ((Primrec.or.comp (test 3) (test 4)).cond
            (Primrec.and.comp (get _ hl) (get _ hr)) (Primrec.const false)))))

theorem noFreeCode_primrec : Primrec noFreeCode := by
  have hg : Primrec₂ (fun (_ : Unit) (h : List Bool) => some (noFreeStep h)) :=
    ((Primrec.option_some.comp noFreeStep_primrec).comp Primrec.snd).to₂
  have htable := Primrec.nat_strong_rec (fun (_ : Unit) c => noFreeCode c) hg (by
    intro a c
    cases c with
    | zero => simp [noFreeStep, noFreeCode]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [noFreeStep, noFreeCode, hp, hl, hr])
  exact htable.comp (Primrec.const ()) Primrec.id

@[simp] theorem noFreeCode_code {n : Nat} (t : Syntax n) :
    noFreeCode (code t) = true ↔ t.varFinsetLeft = ∅ := by
  induction t with
  | var v => cases v <;> simp [code, toLiteral, variableCode, Term.code,
      noFreeCode, Nat.unpair_pair]
  | func f ts ih =>
    cases f <;> simp_all [code, toLiteral, Term.code, noFreeCode, Nat.unpair_pair,
      FirstOrder.Language.Term.varFinsetLeft, biUnion_empty_iff]

end NativeTerm

namespace NativeTuple

def noFreeCode (c : Nat) : Bool :=
  ((Encodable.decode₂ (List Nat) c).map (fun cs => cs.all NativeTerm.noFreeCode)).getD false

theorem noFreeCode_primrec : Primrec noFreeCode := by
  have hp : PrimrecPred (fun c => NativeTerm.noFreeCode c = true) :=
    Primrec.eq.comp NativeTerm.noFreeCode_primrec (Primrec.const true)
  have ha : Primrec (fun cs : List Nat => cs.all NativeTerm.noFreeCode) := by
    simpa only [← List.all_eq_true, Bool.decide_eq_true] using hp.forall_mem_list.decide
  exact Primrec.option_getD.comp (Primrec.decode₂.option_map (ha.comp Primrec.snd).to₂)
    (Primrec.const false)

@[simp] theorem noFreeCode_code {n m : Nat} (ts : Fin m → NativeTerm.Syntax n) :
    noFreeCode (code ts) = true ↔ ∀ i, (ts i).varFinsetLeft = ∅ := by
  simp [noFreeCode, code, List.all_eq_true]

end NativeTuple

namespace NativeFormula

def noFreeCode : Nat → Bool
  | 0 => false
  | k + 1 =>
    let tag := (k.unpair.2 - 1).unpair.1
    let p := (k.unpair.2 - 1).unpair.2
    cond (tag == 0) true
      (cond (tag == 1) (NativeTerm.noFreeCode p.unpair.1 && NativeTerm.noFreeCode p.unpair.2)
        (cond (tag == 2) (NativeTuple.noFreeCode p.unpair.2)
          (cond (tag == 3) (noFreeCode p.unpair.1 && noFreeCode p.unpair.2)
            (cond (tag == 4) (noFreeCode p) false))))
termination_by c => c
decreasing_by
  all_goals
    have hb := Nat.unpair_right_le k
    have hk := Nat.sub_le k.unpair.2 1
    have hp := Nat.unpair_right_le (k.unpair.2 - 1)
    have hl := Nat.unpair_left_le (k.unpair.2 - 1).unpair.2
    have hr := Nat.unpair_right_le (k.unpair.2 - 1).unpair.2
    omega

private def noFreeStep (h : List Bool) : Bool :=
  let k := h.length - 1
  let tag := (k.unpair.2 - 1).unpair.1
  let p := (k.unpair.2 - 1).unpair.2
  cond (h.length == 0) false
    (cond (tag == 0) true
      (cond (tag == 1) (NativeTerm.noFreeCode p.unpair.1 && NativeTerm.noFreeCode p.unpair.2)
        (cond (tag == 2) (NativeTuple.noFreeCode p.unpair.2)
          (cond (tag == 3) (h[p.unpair.1]?.getD false && h[p.unpair.2]?.getD false)
            (cond (tag == 4) (h[p]?.getD false) false)))))

private theorem noFreeStep_primrec : Primrec noFreeStep := by
  have hk : Primrec (fun h : List Bool => h.length - 1) :=
    Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)
  have hn := Primrec.unpair.comp
    (Primrec.nat_sub.comp (Primrec.snd.comp (Primrec.unpair.comp hk)) (Primrec.const 1))
  have ht := Primrec.fst.comp hn
  have hp := Primrec.snd.comp hn
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have get (f : List Bool → Nat) (hf : Primrec f) :
      Primrec (fun h : List Bool => h[f h]?.getD false) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hf)
      (Primrec.const false)
  exact (Primrec.beq.comp Primrec.list_length (Primrec.const 0)).cond (Primrec.const false)
    ((test 0).cond (Primrec.const true)
      ((test 1).cond (Primrec.and.comp (NativeTerm.noFreeCode_primrec.comp hl)
        (NativeTerm.noFreeCode_primrec.comp hr))
        ((test 2).cond (NativeTuple.noFreeCode_primrec.comp hr)
          ((test 3).cond (Primrec.and.comp (get _ hl) (get _ hr))
            ((test 4).cond (get _ hp) (Primrec.const false))))))

theorem noFreeCode_primrec : Primrec noFreeCode := by
  have hg : Primrec₂ (fun (_ : Unit) (h : List Bool) => some (noFreeStep h)) :=
    ((Primrec.option_some.comp noFreeStep_primrec).comp Primrec.snd).to₂
  have htable := Primrec.nat_strong_rec (fun (_ : Unit) c => noFreeCode c) hg (by
    intro a c
    cases c with
    | zero => simp [noFreeStep, noFreeCode]
    | succ k =>
      have hb := Nat.unpair_right_le k
      have hk := Nat.sub_le k.unpair.2 1
      have hp₀ := Nat.unpair_right_le (k.unpair.2 - 1)
      have hp : (k.unpair.2 - 1).unpair.2 < k + 1 := by omega
      have hl : (k.unpair.2 - 1).unpair.2.unpair.1 < k + 1 :=
        lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : (k.unpair.2 - 1).unpair.2.unpair.2 < k + 1 :=
        lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [noFreeStep, noFreeCode, hp, hl, hr])
  exact htable.comp (Primrec.const ()) Primrec.id

@[simp] theorem noFreeCode_code {n : Nat} (φ : Syntax n) :
    noFreeCode (code φ) = true ↔ φ.freeVarFinset = ∅ := by
  induction φ <;> simp_all [code, noFreeCode, Nat.unpair_pair,
    FirstOrder.Language.BoundedFormula.freeVarFinset, biUnion_empty_iff,
    Finset.union_eq_empty]

theorem closed_primrec (n : Nat) : PrimrecPred (fun φ : Syntax n => φ.freeVarFinset = ∅) :=
  (Primrec.eq.comp (noFreeCode_primrec.comp (code_primrec n)) (Primrec.const true)).of_eq
    (fun φ => noFreeCode_code φ)

end NativeFormula

namespace NativeClosedLabels

abbrev TermSyntax (n : Nat) := (language Nat).Term (Empty ⊕ Fin n)
abbrev Syntax (n : Nat) := (language Nat).BoundedFormula Empty n

def embedTerm {n : Nat} (t : TermSyntax n) : NativeTerm.Syntax n :=
  t.relabel (Sum.map Empty.elim id)

def eraseTerm {n : Nat} (t : NativeTerm.Syntax n) : TermSyntax n :=
  t.subst (Sum.elim (fun _ => .func .zero Fin.elim0) (fun i => .var (.inr i)))

@[simp] theorem eraseTerm_embedTerm {n : Nat} (t : TermSyntax n) :
    eraseTerm (embedTerm t) = t := by
  induction t with
  | var v =>
    cases v with
    | inl e => exact e.elim
    | inr i => rfl
  | func f ts ih =>
    exact congrArg (FirstOrder.Language.Term.func f) (funext ih)

theorem embedTerm_eraseTerm {n : Nat} (t : NativeTerm.Syntax n) :
    t.varFinsetLeft = ∅ → embedTerm (eraseTerm t) = t := by
  induction t with
  | var v =>
    intro h
    cases v with
    | inl x => simp at h
    | inr i => rfl
  | func f ts ih =>
    intro h
    have hs : ∀ i, (ts i).varFinsetLeft = ∅ := (biUnion_empty_iff _).mp h
    simp only [embedTerm, eraseTerm, FirstOrder.Language.Term.relabel,
      FirstOrder.Language.Term.subst]
    apply congrArg (FirstOrder.Language.Term.func f)
    funext i
    exact ih i (hs i)

theorem embedTerm_closed {n : Nat} (t : TermSyntax n) : (embedTerm t).varFinsetLeft = ∅ := by
  induction t with
  | var v =>
    cases v with
    | inl e => exact e.elim
    | inr i => rfl
  | func f ts ih =>
    exact (biUnion_empty_iff _).mpr ih

def embed {n : Nat} (φ : Syntax n) : NativeFormula.Syntax n :=
  φ.mapTermRel (fun _ t => embedTerm t) (fun _ => id) (fun _ => id)

def erase {n : Nat} (φ : NativeFormula.Syntax n) : Syntax n :=
  φ.mapTermRel (fun _ t => eraseTerm t) (fun _ => id) (fun _ => id)

@[simp] theorem erase_embed {n : Nat} (φ : Syntax n) : erase (embed φ) = φ := by
  induction φ <;> simp_all [erase, embed, FirstOrder.Language.BoundedFormula.mapTermRel]

theorem embed_erase {n : Nat} (φ : NativeFormula.Syntax n) :
    φ.freeVarFinset = ∅ → embed (erase φ) = φ := by
  induction φ with
  | falsum => intro _; rfl
  | equal t u =>
    intro h
    have hs := Finset.union_eq_empty.mp h
    simp [erase, embed, FirstOrder.Language.BoundedFormula.mapTermRel,
      embedTerm_eraseTerm t hs.1, embedTerm_eraseTerm u hs.2]
  | rel r ts =>
    intro h
    have hs : ∀ i, (ts i).varFinsetLeft = ∅ := (biUnion_empty_iff _).mp h
    simp [erase, embed, FirstOrder.Language.BoundedFormula.mapTermRel,
      fun i => embedTerm_eraseTerm (ts i) (hs i)]
  | imp φ ψ ihφ ihψ =>
    intro h
    have hs := Finset.union_eq_empty.mp h
    exact congrArg₂ FirstOrder.Language.BoundedFormula.imp (ihφ hs.1) (ihψ hs.2)
  | all φ ih =>
    intro h
    exact congrArg FirstOrder.Language.BoundedFormula.all (ih h)

theorem embed_closed {n : Nat} (φ : Syntax n) : (embed φ).freeVarFinset = ∅ := by
  induction φ <;> simp_all [embed, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.freeVarFinset, embedTerm_closed, biUnion_empty_iff]

def closedEquiv (n : Nat) : Syntax n ≃ {φ : NativeFormula.Syntax n // φ.freeVarFinset = ∅} where
  toFun := fun φ => ⟨embed φ, embed_closed φ⟩
  invFun := fun φ => erase φ.val
  left_inv := erase_embed
  right_inv := fun φ => Subtype.ext (embed_erase φ.val φ.property)

noncomputable instance syntaxPrimcodable (n : Nat) : Primcodable (Syntax n) := by
  letI : Primcodable {φ : NativeFormula.Syntax n // φ.freeVarFinset = ∅} :=
    Primcodable.subtype (NativeFormula.closed_primrec n)
  exact Primcodable.ofEquiv {φ : NativeFormula.Syntax n // φ.freeVarFinset = ∅} (closedEquiv n)

def code {n : Nat} (φ : Syntax n) : Nat := NativeFormula.code (embed φ)

theorem code_injective {n : Nat} : Function.Injective (code (n := n)) := by
  intro φ ψ h
  have he : embed φ = embed ψ := NativeFormula.code_injective h
  exact by simpa only [erase_embed] using congrArg erase he

@[simp] theorem encode_eq_code {n : Nat} (φ : Syntax n) : Encodable.encode φ = code φ := rfl

theorem code_primrec (n : Nat) : Primrec (code (n := n)) := by
  exact Primrec.encode

theorem embed_primrec (n : Nat) : Primrec (embed (n := n)) := by
  apply Primrec.encode_iff.1
  exact code_primrec n

theorem relabelTerm_code {n : Nat} (t : TermSyntax n) :
    NativeTerm.code (t.relabel (FirstOrder.Language.BoundedFormula.relabelAux
      (Sum.inl ∘ (Empty.elim : Empty → Nat) : Empty → Nat ⊕ Fin 0) n)) =
      NativeTerm.code (embedTerm t) := by
  induction t with
  | var v =>
    cases v with
    | inl e => exact e.elim
    | inr i => simp [NativeTerm.code_var, NativeTerm.variableCode, embedTerm,
        FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.relabelAux]
  | func f ts ih =>
    cases f <;> simp_all [NativeTerm.code, NativeTerm.toLiteral, Term.code, embedTerm,
      FirstOrder.Language.Term.relabel]

theorem relabel_code {n : Nat} (φ : Syntax n) :
    NativeFormula.code (FirstOrder.Language.BoundedFormula.relabel
      (Sum.inl ∘ (Empty.elim : Empty → Nat) : Empty → Nat ⊕ Fin 0) φ) = code φ := by
  induction φ <;> simp_all [FirstOrder.Language.BoundedFormula.relabel,
    FirstOrder.Language.BoundedFormula.mapTermRel, NativeFormula.code, code,
    embed, NativeTuple.code, relabelTerm_code]

theorem sentenceFormula_eq_embed (σ : (language Nat).Sentence) :
    FirstOrderCalculus.sentenceFormula σ = embed σ :=
  NativeFormula.code_injective (relabel_code σ)

theorem sentenceFormula_primrec :
    Primrec (FirstOrderCalculus.sentenceFormula (L := language Nat)) :=
  (embed_primrec 0).of_eq (fun σ => (sentenceFormula_eq_embed σ).symm)

def isCodeAt (n c : Nat) : Bool := NativeFormula.isCodeAt n c && NativeFormula.noFreeCode c

theorem isCodeAt_primrec : Primrec₂ isCodeAt :=
  (Primrec.and.comp NativeFormula.isCodeAt_primrec
    (NativeFormula.noFreeCode_primrec.comp Primrec.snd)).to₂

@[simp] theorem isCodeAt_code {n : Nat} (φ : Syntax n) : isCodeAt n (code φ) = true := by
  simp [isCodeAt, code, embed_closed]

theorem isCodeAt_iff (n c : Nat) :
    isCodeAt n c = true ↔ ∃ φ : Syntax n, code φ = c := by
  constructor
  · intro h
    have hs := Bool.and_eq_true_iff.mp h
    obtain ⟨φ, hφ⟩ := NativeFormula.isCodeAt_sound n c hs.1
    have hc : φ.freeVarFinset = ∅ := (NativeFormula.noFreeCode_code φ).mp
      (by simpa only [hφ] using hs.2)
    exact ⟨erase φ, by simpa only [code, embed_erase φ hc] using hφ⟩
  · rintro ⟨φ, rfl⟩
    exact isCodeAt_code φ

noncomputable def decodeExact (n : Nat) : Nat → Option (Syntax n) := Encodable.decode₂ (Syntax n)

theorem decodeExact_primrec (n : Nat) : Primrec (decodeExact n) := Primrec.decode₂

theorem decodeExact_eq_some_iff {n c : Nat} (φ : Syntax n) :
    decodeExact n c = some φ ↔ code φ = c := by
  simpa only [decodeExact, encode_eq_code] using
    (Encodable.decode₂_eq_some (n := c) (a := φ))

@[simp] theorem decodeExact_code {n : Nat} (φ : Syntax n) :
    decodeExact n (code φ) = some φ := (decodeExact_eq_some_iff φ).mpr rfl

end NativeClosedLabels
end Alexander313.Delta
