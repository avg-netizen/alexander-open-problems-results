import Alexander313.Alexander.NativeTermFormation
import Mathlib.Data.List.OfFn

/-!
# Exact primitive-recursive native argument tuples

The tuple code is the ordinary list code of its native term codes. Failsafe
list decoding rejects noncanonical list codes. Both the required arity and
every term's bound context are tested, so a successful recognition constructs
an actual finite native argument tuple.
-/

namespace Alexander313.Delta.NativeTuple

def code {n m : Nat} (ts : Fin m → NativeTerm.Syntax n) : Nat :=
  Encodable.encode (List.ofFn (fun i => NativeTerm.code (ts i)))

private def entries (n : Nat) (cs : List Nat) : Bool := cs.all (NativeTerm.isCode n)

private theorem entries_primrec : Primrec₂ entries := by
  have hp : PrimrecRel (fun c n : Nat => NativeTerm.isCode n c = true) :=
    Primrec.eq.comp (NativeTerm.isCode_primrec.comp Primrec.snd Primrec.fst)
      (Primrec.const true)
  have h := hp.forall_mem_list.decide.comp Primrec.snd Primrec.fst
  apply h.to₂.of_eq
  intro n cs
  simp only [entries, ← List.all_eq_true, Bool.decide_eq_true]

def isCode (n m c : Nat) : Bool :=
  ((Encodable.decode₂ (List Nat) c).map (fun cs => (cs.length == m) && entries n cs)).getD false

theorem isCode_primrec :
    Primrec (fun p : (Nat × Nat) × Nat => isCode p.1.1 p.1.2 p.2) := by
  have hd : Primrec (fun p : (Nat × Nat) × Nat => Encodable.decode₂ (List Nat) p.2) :=
    Primrec.decode₂.comp Primrec.snd
  have hn : Primrec (fun p : ((Nat × Nat) × Nat) × List Nat => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hm : Primrec (fun p : ((Nat × Nat) × Nat) × List Nat => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hg := Primrec.and.comp
    (Primrec.beq.comp (Primrec.list_length.comp Primrec.snd) hm)
    (entries_primrec.comp hn Primrec.snd)
  exact Primrec.option_getD.comp (hd.option_map hg.to₂) (Primrec.const false)

@[simp] theorem isCode_code {n m : Nat} (ts : Fin m → NativeTerm.Syntax n) :
    isCode n m (code ts) = true := by
  simp [isCode, code, entries, List.all_eq_true]

theorem code_injective {n m : Nat} :
    Function.Injective (code (n := n) (m := m)) := by
  intro ts us h
  have hl : List.ofFn (fun i => NativeTerm.code (ts i)) =
      List.ofFn (fun i => NativeTerm.code (us i)) := Encodable.encode_injective h
  have hf := List.ofFn_injective hl
  funext i
  exact NativeTerm.code_injective (congrFun hf i)

theorem isCode_sound (n m c : Nat) (h : isCode n m c = true) :
    ∃ ts : Fin m → NativeTerm.Syntax n, code ts = c := by
  classical
  cases hd : Encodable.decode₂ (List Nat) c with
  | none => simp [isCode, hd] at h
  | some cs =>
    have hs : cs.length = m ∧ ∀ t ∈ cs, NativeTerm.isCode n t = true := by
      simpa [isCode, hd, entries, List.all_eq_true] using h
    have hc : Encodable.encode cs = c := Encodable.decode₂_eq_some.mp hd
    have hm := hs.1
    subst m
    let ts : Fin cs.length → NativeTerm.Syntax n := fun i =>
      Classical.choose (NativeTerm.isCode_sound n (cs.get i)
        (hs.2 _ (List.get_mem cs i)))
    have ht (i : Fin cs.length) : NativeTerm.code (ts i) = cs.get i :=
      Classical.choose_spec (NativeTerm.isCode_sound n (cs.get i)
        (hs.2 _ (List.get_mem cs i)))
    have hl : List.ofFn (fun i => NativeTerm.code (ts i)) = cs := by
      calc
        List.ofFn (fun i => NativeTerm.code (ts i)) = List.ofFn cs.get :=
          congrArg List.ofFn (funext ht)
        _ = cs := List.ofFn_get cs
    exact ⟨ts, by simpa only [code, hl] using hc⟩

theorem isCode_iff (n m c : Nat) :
    isCode n m c = true ↔ ∃ ts : Fin m → NativeTerm.Syntax n, code ts = c :=
  ⟨isCode_sound n m c, by rintro ⟨ts, rfl⟩; exact isCode_code ts⟩

end Alexander313.Delta.NativeTuple
