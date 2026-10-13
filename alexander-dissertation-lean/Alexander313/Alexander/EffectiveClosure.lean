import Alexander313.Alexander.EffectiveDelta
import Alexander313.Alexander.FirstOrderClosure

/-!
# Literal primitive-recursive native sorted universal sentences

The variable list is the actual increasing native free-variable set. Free
leaves are replaced by their list positions, old bound levels are shifted by
the list length, and `alls` is coded by the actual decreasing context headers.
The result agrees with the existing restrict/sort/relabel construction.
-/

namespace Alexander313.Delta.NativeClosure

def memberCode (x c : Nat) : Bool := decide (x ∈ NativeFormula.variablesCode c)

theorem memberCode_primrec : Primrec₂ memberCode := by
  have he : PrimrecRel (fun x y : Nat => x = y) := Primrec.eq
  have hp := he.exists_mem_list.comp (NativeFormula.variablesCode_primrec.comp Primrec.snd) Primrec.fst
  exact (hp.decide.of_eq (g := fun p : Nat × Nat => memberCode p.1 p.2)
    (fun p => by simp [memberCode])).to₂

def sortedCode (c : Nat) : List Nat :=
  (List.range (NativeFormula.freshCode c)).filter (fun x => memberCode x c)

theorem sortedCode_primrec : Primrec sortedCode := by
  have hm : PrimrecRel (fun x c : Nat => memberCode x c = true) :=
    Primrec.eq.comp memberCode_primrec (Primrec.const true)
  exact (hm.listFilter.comp (Primrec.list_range.comp NativeFormula.freshCode_primrec)
    Primrec.id).of_eq (fun n => by simp [sortedCode])

theorem sortedCode_toFinset (φ : NativeFormula.Syntax 0) :
    (sortedCode (NativeFormula.code φ)).toFinset = φ.freeVarFinset := by
  ext x
  simp only [sortedCode, List.mem_toFinset, List.mem_filter, List.mem_range,
    memberCode, decide_eq_true_eq, NativeFormula.mem_variablesCode_code]
  exact ⟨fun h => h.2, fun hx => ⟨NativeFormula.freeVar_lt_fresh φ hx, hx⟩⟩

@[simp] theorem sortedCode_code (φ : NativeFormula.Syntax 0) :
    sortedCode (NativeFormula.code φ) = φ.freeVarFinset.sort (· ≤ ·) := by
  have hn : (sortedCode (NativeFormula.code φ)).Nodup := List.nodup_range.filter _
  have hp : List.Perm (sortedCode (NativeFormula.code φ)) (φ.freeVarFinset.sort (· ≤ ·)) :=
    List.perm_of_nodup_nodup_toFinset_eq hn (φ.freeVarFinset.sort_nodup (· ≤ ·))
      (by rw [sortedCode_toFinset, Finset.sort_toFinset])
  exact hp.eq_of_pairwise' (List.pairwise_le_range.filter _) (φ.freeVarFinset.pairwise_sort (· ≤ ·))

def abstractVariableCode (cs : List Nat) (p : Nat) : Nat :=
  EncodedSyntax.node 0 (Nat.pair 1 (cond (p.unpair.1 == 0)
    (cs.idxOf p.unpair.2) (cs.length + p.unpair.2)))

theorem abstractVariableCode_primrec : Primrec₂ abstractVariableCode := by
  have hp := Primrec.unpair.comp (Primrec.snd : Primrec (Prod.snd : List Nat × Nat → _))
  have ht := Primrec.fst.comp hp
  have hx := Primrec.snd.comp hp
  have hi := (Primrec.beq.comp ht (Primrec.const 0)).cond
    (Primrec.list_idxOf.comp hx Primrec.fst)
    (Primrec.nat_add.comp (Primrec.list_length.comp Primrec.fst) hx)
  exact (EncodedSyntax.node_primrec.comp (Primrec.const 0)
    (Primrec₂.natPair.comp (Primrec.const 1) hi)).to₂

private theorem abstractTerm_restrict (cs : List Nat) {d n : Nat}
    (hd : cs.length = d) (t : NativeTerm.Syntax n)
    (f : t.varFinsetLeft → Fin d) (hf : ∀ x, cs.idxOf x.val = (f x).val) :
    NativeTerm.rewriteCode abstractVariableCode cs (NativeTerm.code t) = NativeTerm.code
      (NativeClosedLabels.embedTerm ((t.restrictVarLeft f).relabel
        (FirstOrder.Language.BoundedFormula.relabelAux (Sum.inr : Fin d → Empty ⊕ Fin d) n))) := by
  subst d
  revert f
  induction t with
  | var v =>
    intro f hf
    cases v with
    | inl x =>
      have h := hf ⟨x, Finset.mem_singleton_self x⟩
      simpa [NativeTerm.rewriteCode, abstractVariableCode, NativeTerm.code,
        NativeTerm.toLiteral, NativeTerm.variableCode, Term.code,
        FirstOrder.Language.Term.restrictVarLeft, NativeClosedLabels.embedTerm,
        FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.relabelAux,
        Nat.unpair_pair, EncodedSyntax.node] using
        congrArg (fun i => EncodedSyntax.node 0 (Nat.pair 1 i)) h
    | inr i =>
      simp [NativeTerm.rewriteCode, abstractVariableCode, NativeTerm.code,
        NativeTerm.toLiteral, NativeTerm.variableCode, Term.code,
        FirstOrder.Language.Term.restrictVarLeft, NativeClosedLabels.embedTerm,
        FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.relabelAux,
        Nat.unpair_pair, EncodedSyntax.node]
  | func g ts ih =>
    intro f hf
    have ht (i) := ih i
      (f ∘ Set.inclusion (Finset.subset_biUnion_of_mem
        (fun i => (ts i).varFinsetLeft) (Finset.mem_univ i)))
      (fun x => hf (Set.inclusion (Finset.subset_biUnion_of_mem
        (fun i => (ts i).varFinsetLeft) (Finset.mem_univ i)) x))
    cases g <;> simp_all [NativeTerm.rewriteCode, NativeTerm.code, NativeTerm.toLiteral,
      Term.code, FirstOrder.Language.Term.restrictVarLeft, NativeClosedLabels.embedTerm,
      FirstOrder.Language.Term.relabel, Nat.unpair_pair, EncodedSyntax.node, Function.comp_def]

private theorem abstractFormula_restrict (cs : List Nat) {d n : Nat}
    (hd : cs.length = d) (φ : NativeFormula.Syntax n)
    (f : φ.freeVarFinset → Fin d) (hf : ∀ x, cs.idxOf x.val = (f x).val) :
    NativeFormula.rewriteCode (NativeTerm.rewriteCode abstractVariableCode) d cs (NativeFormula.code φ) =
      NativeClosedLabels.code ((φ.restrictFreeVar f).relabel
        (Sum.inr : Fin d → Empty ⊕ Fin d)) := by
  revert f
  induction φ with
  | falsum =>
    intro f hf
    simp [NativeFormula.rewriteCode, NativeFormula.code, NativeClosedLabels.code,
      NativeClosedLabels.embed, FirstOrder.Language.BoundedFormula.restrictFreeVar,
      FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
      Nat.unpair_pair]
  | equal t u =>
    intro f hf
    have ht := abstractTerm_restrict cs hd t
      (f ∘ Set.inclusion Finset.subset_union_left)
      (fun x => hf (Set.inclusion Finset.subset_union_left x))
    have hu := abstractTerm_restrict cs hd u
      (f ∘ Set.inclusion Finset.subset_union_right)
      (fun x => hf (Set.inclusion Finset.subset_union_right x))
    simp [NativeFormula.rewriteCode, NativeFormula.code, NativeClosedLabels.code,
      NativeClosedLabels.embed, FirstOrder.Language.BoundedFormula.restrictFreeVar,
      FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
      Nat.unpair_pair, ht, hu]
  | rel r ts =>
    intro f hf
    have ht (i) := abstractTerm_restrict cs hd (ts i)
      (f ∘ Set.inclusion (Finset.subset_biUnion_of_mem
        (fun i => (ts i).varFinsetLeft) (Finset.mem_univ i)))
      (fun x => hf (Set.inclusion (Finset.subset_biUnion_of_mem
        (fun i => (ts i).varFinsetLeft) (Finset.mem_univ i)) x))
    let us := fun i => NativeClosedLabels.embedTerm (((ts i).restrictVarLeft
      (f ∘ Set.inclusion (Finset.subset_biUnion_of_mem
        (fun j => (ts j).varFinsetLeft) (Finset.mem_univ i)))).relabel
          (FirstOrder.Language.BoundedFormula.relabelAux (Sum.inr : Fin d → Empty ⊕ Fin d) _))
    have hs : NativeTuple.rewriteCode (NativeTerm.rewriteCode abstractVariableCode) cs
        (NativeTuple.code ts) = NativeTuple.code us := by
      simp only [NativeTuple.rewriteCode, NativeTuple.code,
        Encodable.decode₂_encode, Option.getD_some, List.map_ofFn]
      exact congrArg Encodable.encode (congrArg List.ofFn (funext ht))
    simp [NativeFormula.rewriteCode, NativeFormula.code, NativeClosedLabels.code,
      NativeClosedLabels.embed, FirstOrder.Language.BoundedFormula.restrictFreeVar,
      FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
      Nat.unpair_pair, hs, us]
  | imp φ ψ ihφ ihψ =>
    intro f hf
    have hφ := ihφ (f ∘ Set.inclusion Finset.subset_union_left)
      (fun x => hf (Set.inclusion Finset.subset_union_left x))
    have hψ := ihψ (f ∘ Set.inclusion Finset.subset_union_right)
      (fun x => hf (Set.inclusion Finset.subset_union_right x))
    simp [NativeFormula.rewriteCode, NativeFormula.code, NativeClosedLabels.code,
      NativeClosedLabels.embed, FirstOrder.Language.BoundedFormula.restrictFreeVar,
      FirstOrder.Language.BoundedFormula.relabel_imp, FirstOrder.Language.BoundedFormula.mapTermRel,
      Nat.unpair_pair, hφ, hψ]
  | all φ ih =>
    intro f hf
    have h := ih f hf
    simp only [FirstOrder.Language.BoundedFormula.restrictFreeVar,
      FirstOrder.Language.BoundedFormula.relabel_all]
    simpa [NativeFormula.rewriteCode, NativeFormula.code, NativeClosedLabels.code,
      NativeClosedLabels.embed, FirstOrder.Language.BoundedFormula.mapTermRel,
      Nat.unpair_pair, h, Nat.add_assoc] using
      congrArg (fun c => nativeNode (d + n) 4 c) h

def allsCode (n c : Nat) : Nat :=
  (List.range n).foldr (fun i c => nativeNode i 4 c) c

theorem allsCode_primrec : Primrec₂ allsCode :=
  (Primrec.list_foldr (Primrec.list_range.comp Primrec.fst) Primrec.snd
    (nativeNode_primrec.comp
      (((Primrec.fst.comp Primrec.snd).pair (Primrec.const 4)).pair
        (Primrec.snd.comp Primrec.snd))).to₂).to₂

@[simp] theorem allsCode_succ (n c : Nat) :
    allsCode (n + 1) c = allsCode n (nativeNode n 4 c) := by
  simp [allsCode, List.range_succ, List.foldr_append]

theorem allsCode_code {n : Nat} (φ : NativeClosedLabels.Syntax n) :
    allsCode n (NativeClosedLabels.code φ) = NativeClosedLabels.code φ.alls := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [allsCode_succ]
    change allsCode n (NativeClosedLabels.code φ.all) =
      NativeClosedLabels.code φ.all.alls
    exact ih φ.all

def universalSentenceCode (c : Nat) : Nat :=
  let cs := sortedCode c
  allsCode cs.length (NativeFormula.rewriteCode
    (NativeTerm.rewriteCode abstractVariableCode) cs.length cs c)

theorem universalSentenceCode_primrec : Primrec universalSentenceCode := by
  have hs := sortedCode_primrec
  have hl := Primrec.list_length.comp hs
  have hr := NativeFormula.rewriteCode_uniform_primrec
    (NativeTerm.rewriteCode_primrec abstractVariableCode_primrec)
  exact allsCode_primrec.comp hl (hr.comp ((hl.pair hs).pair Primrec.id))

private theorem restrictTerm_relabel_congr {β γ δ : Type} {d n : Nat}
    (t : NativeTerm.Syntax n) (f : t.varFinsetLeft → β) (f' : t.varFinsetLeft → γ)
    (g : β → δ ⊕ Fin d) (g' : γ → δ ⊕ Fin d) (h : ∀ x, g (f x) = g' (f' x)) :
    (t.restrictVarLeft f).relabel (FirstOrder.Language.BoundedFormula.relabelAux g n) =
      (t.restrictVarLeft f').relabel (FirstOrder.Language.BoundedFormula.relabelAux g' n) := by
  revert f f'
  induction t with
  | var v =>
    intro f f' h
    cases v with
    | inl x =>
      have hx := h ⟨x, Finset.mem_singleton_self x⟩
      simp only [FirstOrder.Language.Term.restrictVarLeft, FirstOrder.Language.Term.relabel,
        FirstOrder.Language.BoundedFormula.relabelAux, Function.comp_def, Sum.map_inl]
      erw [hx]
    | inr i => rfl
  | func sym ts ih =>
    intro f f' h
    change FirstOrder.Language.Term.func sym (fun i => ((ts i).restrictVarLeft
      (f ∘ Set.inclusion (Finset.subset_biUnion_of_mem (fun j => (ts j).varFinsetLeft) (Finset.mem_univ i)))).relabel
        (FirstOrder.Language.BoundedFormula.relabelAux g n)) =
      FirstOrder.Language.Term.func sym (fun i => ((ts i).restrictVarLeft
        (f' ∘ Set.inclusion (Finset.subset_biUnion_of_mem (fun j => (ts j).varFinsetLeft) (Finset.mem_univ i)))).relabel
          (FirstOrder.Language.BoundedFormula.relabelAux g' n))
    congr 1
    funext i
    exact ih i _ _ (fun x => h (Set.inclusion
      (Finset.subset_biUnion_of_mem (fun j => (ts j).varFinsetLeft) (Finset.mem_univ i)) x))

private theorem restrictFormula_relabel_congr {β γ δ : Type} {d n : Nat}
    (φ : NativeFormula.Syntax n) (f : φ.freeVarFinset → β) (f' : φ.freeVarFinset → γ)
    (g : β → δ ⊕ Fin d) (g' : γ → δ ⊕ Fin d) (h : ∀ x, g (f x) = g' (f' x)) :
    (φ.restrictFreeVar f).relabel g = (φ.restrictFreeVar f').relabel g' := by
  revert f f'
  induction φ with
  | falsum => intros; rfl
  | equal t u =>
    intro f f' h
    have ht := restrictTerm_relabel_congr t
      (f ∘ Set.inclusion Finset.subset_union_left)
      (f' ∘ Set.inclusion Finset.subset_union_left) g g'
      (fun x => h (Set.inclusion Finset.subset_union_left x))
    have hu := restrictTerm_relabel_congr u
      (f ∘ Set.inclusion Finset.subset_union_right)
      (f' ∘ Set.inclusion Finset.subset_union_right) g g'
      (fun x => h (Set.inclusion Finset.subset_union_right x))
    exact congrArg₂ FirstOrder.Language.BoundedFormula.equal ht hu
  | rel r ts =>
    intro f f' h
    have ht (i) := restrictTerm_relabel_congr (ts i)
      (f ∘ Set.inclusion (Finset.subset_biUnion_of_mem (fun j => (ts j).varFinsetLeft) (Finset.mem_univ i)))
      (f' ∘ Set.inclusion (Finset.subset_biUnion_of_mem (fun j => (ts j).varFinsetLeft) (Finset.mem_univ i))) g g'
      (fun x => h (Set.inclusion
        (Finset.subset_biUnion_of_mem (fun j => (ts j).varFinsetLeft) (Finset.mem_univ i)) x))
    exact congrArg (FirstOrder.Language.BoundedFormula.rel (L := language Nat) r) (funext ht)
  | imp φ ψ ihφ ihψ =>
    intro f f' h
    have hφ := ihφ (f ∘ Set.inclusion Finset.subset_union_left)
      (f' ∘ Set.inclusion Finset.subset_union_left)
      (fun x => h (Set.inclusion Finset.subset_union_left x))
    have hψ := ihψ (f ∘ Set.inclusion Finset.subset_union_right)
      (f' ∘ Set.inclusion Finset.subset_union_right)
      (fun x => h (Set.inclusion Finset.subset_union_right x))
    exact congrArg₂ FirstOrder.Language.BoundedFormula.imp hφ hψ
  | all φ ih =>
    intro f f' h
    simp only [FirstOrder.Language.BoundedFormula.restrictFreeVar,
      FirstOrder.Language.BoundedFormula.relabel_all, ih f f' h]

@[simp] theorem universalSentenceCode_code (φ : NativeFormula.Syntax 0) :
    universalSentenceCode (NativeFormula.code φ) =
      NativeClosedLabels.code (FirstOrderClosure.universalSentence φ) := by
  let cs := sortedCode (NativeFormula.code φ)
  have hd : cs.length = φ.freeVarFinset.card := by simp [cs]
  have hf (x : φ.freeVarFinset) : cs.idxOf x.val =
      ((φ.freeVarFinset.orderIsoOfFin rfl).symm x).val := by
    simpa only [cs, sortedCode_code] using
      (Finset.orderIsoOfFin_symm_apply φ.freeVarFinset rfl x).symm
  have h := abstractFormula_restrict cs hd φ
    (fun x => (φ.freeVarFinset.orderIsoOfFin rfl).symm x) hf
  unfold universalSentenceCode FirstOrderClosure.universalSentence
  change allsCode cs.length (NativeFormula.rewriteCode
    (NativeTerm.rewriteCode abstractVariableCode) cs.length cs (NativeFormula.code φ)) = _
  rw [hd, h, allsCode_code]
  congr 1
  exact congrArg FirstOrder.Language.BoundedFormula.alls
    (restrictFormula_relabel_congr φ
      (fun x => (φ.freeVarFinset.orderIsoOfFin rfl).symm x) id
      (Sum.inr : Fin φ.freeVarFinset.card → Empty ⊕ Fin φ.freeVarFinset.card)
      (fun x => Sum.inr ((φ.freeVarFinset.orderIsoOfFin rfl).symm x)) (fun _ => rfl))

end Alexander313.Delta.NativeClosure

namespace Alexander313.FirstOrderClosure

theorem universalSentence_primrec : Primrec
    (universalSentence (L := Delta.language Nat)) := by
  apply Primrec.encode_iff.1
  simpa only [Delta.NativeClosedLabels.encode_eq_code, Delta.NativeClosure.universalSentenceCode_code]
    using Delta.NativeClosure.universalSentenceCode_primrec.comp (Delta.NativeFormula.code_primrec 0)

end Alexander313.FirstOrderClosure
