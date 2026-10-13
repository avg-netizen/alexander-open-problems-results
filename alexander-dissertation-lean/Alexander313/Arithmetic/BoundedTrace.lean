import Alexander313.Arithmetic.SequenceCoding

/-!
# Actual finite witnesses for the universal bounded evaluator

The indexed trace datatype follows the pinned `Code.evaln` equations,
including the decreased cutoff in primitive recursion and minimization.
Every accepted bounded computation constructs a finite trace, and every
trace gives an accepted bounded computation. Thus `W` has actual finite
execution witnesses, before any arithmetical checker is introduced.

The final beta certificates encode the concrete trace data only. Checking
all local execution rules in one fixed arithmetic formula remains separate.
-/

namespace Alexander313

inductive BoundedTrace : Nat → Program → Nat → Nat → Type where
  | zero (k n : Nat) (hn : n ≤ k) : BoundedTrace (k + 1) .zero n 0
  | succ (k n : Nat) (hn : n ≤ k) : BoundedTrace (k + 1) .succ n (n + 1)
  | left (k n : Nat) (hn : n ≤ k) : BoundedTrace (k + 1) .left n n.unpair.1
  | right (k n : Nat) (hn : n ≤ k) : BoundedTrace (k + 1) .right n n.unpair.2
  | pair (k : Nat) (c d : Program) (n u v : Nat) (hn : n ≤ k)
      (tc : BoundedTrace (k + 1) c n u) (td : BoundedTrace (k + 1) d n v) :
      BoundedTrace (k + 1) (.pair c d) n (Nat.pair u v)
  | comp (k : Nat) (c d : Program) (n u v : Nat) (hn : n ≤ k)
      (td : BoundedTrace (k + 1) d n u) (tc : BoundedTrace (k + 1) c u v) :
      BoundedTrace (k + 1) (.comp c d) n v
  | precZero (k : Nat) (c d : Program) (a v : Nat) (hn : Nat.pair a 0 ≤ k)
      (tc : BoundedTrace (k + 1) c a v) :
      BoundedTrace (k + 1) (.prec c d) (Nat.pair a 0) v
  | precSucc (k : Nat) (c d : Program) (a m u v : Nat)
      (hn : Nat.pair a (m + 1) ≤ k)
      (tp : BoundedTrace k (.prec c d) (Nat.pair a m) u)
      (td : BoundedTrace (k + 1) d (Nat.pair a (Nat.pair m u)) v) :
      BoundedTrace (k + 1) (.prec c d) (Nat.pair a (m + 1)) v
  | searchZero (k : Nat) (c : Program) (a m : Nat) (hn : Nat.pair a m ≤ k)
      (tc : BoundedTrace (k + 1) c (Nat.pair a m) 0) :
      BoundedTrace (k + 1) (.rfind' c) (Nat.pair a m) m
  | searchSucc (k : Nat) (c : Program) (a m z v : Nat) (hn : Nat.pair a m ≤ k)
      (tc : BoundedTrace (k + 1) c (Nat.pair a m) (z + 1))
      (ts : BoundedTrace k (.rfind' c) (Nat.pair a (m + 1)) v) :
      BoundedTrace (k + 1) (.rfind' c) (Nat.pair a m) v

namespace BoundedTrace

theorem evaln_mem {k : Nat} {c : Program} {n v : Nat} (t : BoundedTrace k c n v) :
    v ∈ Nat.Partrec.Code.evaln k c n := by
  induction t with
  | zero k n hn => simp [Nat.Partrec.Code.evaln, hn]
  | succ k n hn => simp [Nat.Partrec.Code.evaln, hn]
  | left k n hn => simp [Nat.Partrec.Code.evaln, hn]
  | right k n hn => simp [Nat.Partrec.Code.evaln, hn]
  | pair k c d n u v hn tc td ihc ihd =>
    simp only [Option.mem_def] at ihc ihd
    simp [Nat.Partrec.Code.evaln, hn, ihc, ihd, Seq.seq]
  | comp k c d n u v hn td tc ihd ihc =>
    simp only [Option.mem_def] at ihc ihd
    simp [Nat.Partrec.Code.evaln, hn, ihc, ihd]
  | precZero k c d a v hn tc ihc =>
    simp only [Option.mem_def] at ihc
    simp [Nat.Partrec.Code.evaln, hn, Nat.unpaired, Nat.unpair_pair, ihc]
  | precSucc k c d a m u v hn tp td ihp ihd =>
    simp only [Option.mem_def] at ihp ihd
    simp [Nat.Partrec.Code.evaln, hn, Nat.unpaired, Nat.unpair_pair, ihp, ihd]
  | searchZero k c a m hn tc ihc =>
    simp only [Option.mem_def] at ihc
    simp [Nat.Partrec.Code.evaln, hn, Nat.unpaired, Nat.unpair_pair, ihc]
  | searchSucc k c a m z v hn tc ts ihc ihs =>
    simp only [Option.mem_def] at ihc ihs
    simp [Nat.Partrec.Code.evaln, hn, Nat.unpaired, Nat.unpair_pair, ihc, ihs]

theorem eval_mem {k : Nat} {c : Program} {n v : Nat} (t : BoundedTrace k c n v) :
    v ∈ c.eval n := Nat.Partrec.Code.evaln_sound t.evaln_mem

/-- Predecessor-first records contain cutoff, actual program code,
    input and output for every node, ending with the root record. -/
def data : {k : Nat} → {c : Program} → {n v : Nat} → BoundedTrace k c n v → List Nat
  | _, _, _, _, .zero k n _ => [k + 1, Encodable.encode (Nat.Partrec.Code.zero : Program), n, 0]
  | _, _, _, _, .succ k n _ => [k + 1, Encodable.encode (Nat.Partrec.Code.succ : Program), n, n + 1]
  | _, _, _, _, .left k n _ => [k + 1, Encodable.encode (Nat.Partrec.Code.left : Program), n, n.unpair.1]
  | _, _, _, _, .right k n _ => [k + 1, Encodable.encode (Nat.Partrec.Code.right : Program), n, n.unpair.2]
  | _, _, _, _, .pair k c d n u v _ tc td =>
      tc.data ++ td.data ++ [k + 1, Encodable.encode (.pair c d : Program), n, Nat.pair u v]
  | _, _, _, _, .comp k c d n u v _ td tc =>
      td.data ++ tc.data ++ [k + 1, Encodable.encode (.comp c d : Program), n, v]
  | _, _, _, _, .precZero k c d a v _ tc =>
      tc.data ++ [k + 1, Encodable.encode (.prec c d : Program), Nat.pair a 0, v]
  | _, _, _, _, .precSucc k c d a m u v _ tp td =>
      tp.data ++ td.data ++
        [k + 1, Encodable.encode (.prec c d : Program), Nat.pair a (m + 1), v]
  | _, _, _, _, .searchZero k c a m _ tc =>
      tc.data ++ [k + 1, Encodable.encode (.rfind' c : Program), Nat.pair a m, m]
  | _, _, _, _, .searchSucc k c a m z v _ tc ts =>
      tc.data ++ ts.data ++ [k + 1, Encodable.encode (.rfind' c : Program), Nat.pair a m, v]

theorem data_pa_certificates {k : Nat} {c : Program} {n v : Nat}
    (t : BoundedTrace k c n v) (Owner : Type) :
    ∃ a b, ∀ i : Fin t.data.length,
      Provable (PAInstance Owner) ((betaGraph Owner).close (betaAssignment a b i t.data[i])) :=
  finite_sequence_pa_certificates Owner t.data

end BoundedTrace

/-- Construct a finite indexed trace from the actual accepted bounded
    evaluation, following its structural-code and decreased-cutoff recursion. -/
theorem boundedTrace_of_evaln : ∀ {k : Nat} {c : Program} {n v : Nat},
    v ∈ Nat.Partrec.Code.evaln k c n → Nonempty (BoundedTrace k c n v)
  | 0, c, n, v, h => by simp [Nat.Partrec.Code.evaln, Option.bind_eq_some_iff] at h
  | k + 1, c, n, v, h => by
    induction c generalizing n v with
    | zero =>
      simp [Nat.Partrec.Code.evaln, Option.bind_eq_some_iff] at h
      obtain ⟨hn, rfl⟩ := h
      exact ⟨BoundedTrace.zero k n hn⟩
    | succ =>
      simp [Nat.Partrec.Code.evaln, Option.bind_eq_some_iff] at h
      obtain ⟨hn, rfl⟩ := h
      exact ⟨BoundedTrace.succ k n hn⟩
    | left =>
      simp [Nat.Partrec.Code.evaln, Option.bind_eq_some_iff] at h
      obtain ⟨hn, rfl⟩ := h
      exact ⟨BoundedTrace.left k n hn⟩
    | right =>
      simp [Nat.Partrec.Code.evaln, Option.bind_eq_some_iff] at h
      obtain ⟨hn, rfl⟩ := h
      exact ⟨BoundedTrace.right k n hn⟩
    | pair c d ihc ihd =>
      simp [Nat.Partrec.Code.evaln, Option.bind_eq_some_iff, Seq.seq] at h
      obtain ⟨hn, u, hu, w, hw, rfl⟩ := h
      obtain ⟨tc⟩ := ihc _ _ hu
      obtain ⟨td⟩ := ihd _ _ hw
      exact ⟨BoundedTrace.pair k c d n u w hn tc td⟩
    | comp c d ihc ihd =>
      simp [Nat.Partrec.Code.evaln, Option.bind_eq_some_iff] at h
      obtain ⟨hn, u, hu, hv⟩ := h
      obtain ⟨td⟩ := ihd _ _ hu
      obtain ⟨tc⟩ := ihc _ _ hv
      exact ⟨BoundedTrace.comp k c d n u v hn td tc⟩
    | prec c d ihc ihd =>
      have hex : ∃ a m, n = Nat.pair a m :=
        ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
      obtain ⟨a, m, rfl⟩ := hex
      cases m with
      | zero =>
        simp [Nat.Partrec.Code.evaln, Nat.unpaired, Nat.unpair_pair,
          Option.bind_eq_some_iff] at h
        obtain ⟨hn, hc⟩ := h
        obtain ⟨tc⟩ := ihc _ _ hc
        exact ⟨BoundedTrace.precZero k c d a v hn tc⟩
      | succ m =>
        simp [Nat.Partrec.Code.evaln, Nat.unpaired, Nat.unpair_pair,
          Option.bind_eq_some_iff] at h
        obtain ⟨hn, u, hu, hv⟩ := h
        obtain ⟨tp⟩ := boundedTrace_of_evaln hu
        obtain ⟨td⟩ := ihd _ _ hv
        exact ⟨BoundedTrace.precSucc k c d a m u v hn tp td⟩
    | rfind' c ihc =>
      have hex : ∃ a m, n = Nat.pair a m :=
        ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
      obtain ⟨a, m, rfl⟩ := hex
      simp [Nat.Partrec.Code.evaln, Nat.unpaired, Nat.unpair_pair,
        Option.bind_eq_some_iff] at h
      obtain ⟨hn, z, hz, hrest⟩ := h
      by_cases hz0 : z = 0
      · subst z
        simp at hrest
        subst v
        obtain ⟨tc⟩ := ihc _ _ hz
        exact ⟨BoundedTrace.searchZero k c a m hn tc⟩
      · obtain ⟨w, rfl⟩ : ∃ w, z = w + 1 := ⟨z - 1, by omega⟩
        simp at hrest
        obtain ⟨tc⟩ := ihc _ _ hz
        obtain ⟨ts⟩ := boundedTrace_of_evaln hrest
        exact ⟨BoundedTrace.searchSucc k c a m w v hn tc ts⟩

theorem evaln_iff_boundedTrace (k : Nat) (c : Program) (n v : Nat) :
    v ∈ Nat.Partrec.Code.evaln k c n ↔ Nonempty (BoundedTrace k c n v) :=
  ⟨boundedTrace_of_evaln, fun ⟨t⟩ => t.evaln_mem⟩

theorem W_iff_boundedTrace (e n : Nat) :
    W e n ↔ ∃ k v, Nonempty (BoundedTrace k (Nat.Partrec.Code.ofNatCode e) n v) := by
  rw [W_iff_finite_computation]
  exact exists_congr fun k => exists_congr fun v => evaln_iff_boundedTrace k _ n v

end Alexander313
