import Alexander313.Arithmetic.BoundedTrace

/-!
# Finite predecessor-first execution sequences

Local rules are explicit instances of the ten bounded-evaluator rules.
A certified list admits a record only after all required children occur in
its prefix. Lists are constructed from actual finite traces and conversely
yield those traces. This is the semantic finite object whose beta coding
will be checked by the fixed arithmetic execution formula.
-/

namespace Alexander313

local instance : DecidableEq Program := Encodable.decidableEqOfEncodable Program

structure TraceRecord where
  fuel : Nat
  program : Program
  input : Nat
  output : Nat
  deriving DecidableEq

namespace TraceRecord

def code (r : TraceRecord) : Nat :=
  Nat.pair r.fuel (Nat.pair (Encodable.encode r.program) (Nat.pair r.input r.output))

def decode (n : Nat) : TraceRecord :=
  ⟨n.unpair.1, Nat.Partrec.Code.ofNatCode n.unpair.2.unpair.1,
    n.unpair.2.unpair.2.unpair.1, n.unpair.2.unpair.2.unpair.2⟩

@[simp] theorem decode_code (r : TraceRecord) : decode r.code = r := by
  have hp : Nat.Partrec.Code.ofNatCode (Encodable.encode r.program) = r.program :=
    Denumerable.ofNat_encode r.program
  cases r
  simp [code, decode, Nat.unpair_pair, hp]

@[simp] theorem code_decode (n : Nat) : (decode n).code = n := by
  have hp : Encodable.encode (Nat.Partrec.Code.ofNatCode n.unpair.2.unpair.1) =
      n.unpair.2.unpair.1 := by
    simpa only [Nat.Partrec.Code.ofNatCode_eq] using
      (Denumerable.encode_ofNat (α := Program) n.unpair.2.unpair.1)
  simp only [code, decode, hp, Nat.pair_unpair]

theorem code_injective : Function.Injective code := by
  intro r s h
  simpa only [decode_code] using congrArg decode h

end TraceRecord

inductive LocalTraceStep (earlier : TraceRecord → Prop) : TraceRecord → Prop where
  | zero (k n : Nat) (hn : n ≤ k) : LocalTraceStep earlier ⟨k + 1, .zero, n, 0⟩
  | succ (k n : Nat) (hn : n ≤ k) : LocalTraceStep earlier ⟨k + 1, .succ, n, n + 1⟩
  | left (k n : Nat) (hn : n ≤ k) : LocalTraceStep earlier ⟨k + 1, .left, n, n.unpair.1⟩
  | right (k n : Nat) (hn : n ≤ k) : LocalTraceStep earlier ⟨k + 1, .right, n, n.unpair.2⟩
  | pair (k : Nat) (c d : Program) (n u v : Nat) (hn : n ≤ k)
      (hc : earlier ⟨k + 1, c, n, u⟩) (hd : earlier ⟨k + 1, d, n, v⟩) :
      LocalTraceStep earlier ⟨k + 1, .pair c d, n, Nat.pair u v⟩
  | comp (k : Nat) (c d : Program) (n u v : Nat) (hn : n ≤ k)
      (hd : earlier ⟨k + 1, d, n, u⟩) (hc : earlier ⟨k + 1, c, u, v⟩) :
      LocalTraceStep earlier ⟨k + 1, .comp c d, n, v⟩
  | precZero (k : Nat) (c d : Program) (a v : Nat) (hn : Nat.pair a 0 ≤ k)
      (hc : earlier ⟨k + 1, c, a, v⟩) :
      LocalTraceStep earlier ⟨k + 1, .prec c d, Nat.pair a 0, v⟩
  | precSucc (k : Nat) (c d : Program) (a m u v : Nat) (hn : Nat.pair a (m + 1) ≤ k)
      (hp : earlier ⟨k, .prec c d, Nat.pair a m, u⟩)
      (hd : earlier ⟨k + 1, d, Nat.pair a (Nat.pair m u), v⟩) :
      LocalTraceStep earlier ⟨k + 1, .prec c d, Nat.pair a (m + 1), v⟩
  | searchZero (k : Nat) (c : Program) (a m : Nat) (hn : Nat.pair a m ≤ k)
      (hc : earlier ⟨k + 1, c, Nat.pair a m, 0⟩) :
      LocalTraceStep earlier ⟨k + 1, .rfind' c, Nat.pair a m, m⟩
  | searchSucc (k : Nat) (c : Program) (a m z v : Nat) (hn : Nat.pair a m ≤ k)
      (hc : earlier ⟨k + 1, c, Nat.pair a m, z + 1⟩)
      (hs : earlier ⟨k, .rfind' c, Nat.pair a (m + 1), v⟩) :
      LocalTraceStep earlier ⟨k + 1, .rfind' c, Nat.pair a m, v⟩

theorem LocalTraceStep.mono {P Q : TraceRecord → Prop} {r : TraceRecord}
    (h : LocalTraceStep P r) (hp : ∀ s, P s → Q s) : LocalTraceStep Q r := by
  cases h with
  | zero k n hn => exact .zero k n hn
  | succ k n hn => exact .succ k n hn
  | left k n hn => exact .left k n hn
  | right k n hn => exact .right k n hn
  | pair k c d n u v hn hc hd => exact .pair k c d n u v hn (hp _ hc) (hp _ hd)
  | comp k c d n u v hn hd hc => exact .comp k c d n u v hn (hp _ hd) (hp _ hc)
  | precZero k c d a v hn hc => exact .precZero k c d a v hn (hp _ hc)
  | precSucc k c d a m u v hn hc hd => exact .precSucc k c d a m u v hn (hp _ hc) (hp _ hd)
  | searchZero k c a m hn hc => exact .searchZero k c a m hn (hp _ hc)
  | searchSucc k c a m z v hn hc hs => exact .searchSucc k c a m z v hn (hp _ hc) (hp _ hs)

theorem LocalTraceStep.trace {P : TraceRecord → Prop} {r : TraceRecord}
    (h : LocalTraceStep P r)
    (hp : ∀ s, P s → Nonempty (BoundedTrace s.fuel s.program s.input s.output)) :
    Nonempty (BoundedTrace r.fuel r.program r.input r.output) := by
  cases h with
  | zero k n hn => exact ⟨.zero k n hn⟩
  | succ k n hn => exact ⟨.succ k n hn⟩
  | left k n hn => exact ⟨.left k n hn⟩
  | right k n hn => exact ⟨.right k n hn⟩
  | pair k c d n u v hn hc hd =>
    obtain ⟨tc⟩ := hp _ hc
    obtain ⟨td⟩ := hp _ hd
    exact ⟨.pair k c d n u v hn tc td⟩
  | comp k c d n u v hn hd hc =>
    obtain ⟨td⟩ := hp _ hd
    obtain ⟨tc⟩ := hp _ hc
    exact ⟨.comp k c d n u v hn td tc⟩
  | precZero k c d a v hn hc =>
    obtain ⟨tc⟩ := hp _ hc
    exact ⟨.precZero k c d a v hn tc⟩
  | precSucc k c d a m u v hn hc hd =>
    obtain ⟨tc⟩ := hp _ hc
    obtain ⟨td⟩ := hp _ hd
    exact ⟨.precSucc k c d a m u v hn tc td⟩
  | searchZero k c a m hn hc =>
    obtain ⟨tc⟩ := hp _ hc
    exact ⟨.searchZero k c a m hn tc⟩
  | searchSucc k c a m z v hn hc hs =>
    obtain ⟨tc⟩ := hp _ hc
    obtain ⟨ts⟩ := hp _ hs
    exact ⟨.searchSucc k c a m z v hn tc ts⟩

inductive CertifiedTraceSequence : List TraceRecord → Prop where
  | nil : CertifiedTraceSequence []
  | snoc {Γ : List TraceRecord} (hΓ : CertifiedTraceSequence Γ) (r : TraceRecord)
      (hr : LocalTraceStep (fun s => s ∈ Γ) r) : CertifiedTraceSequence (Γ ++ [r])

namespace CertifiedTraceSequence

theorem append {Γ Δ : List TraceRecord} (hΓ : CertifiedTraceSequence Γ)
    (hΔ : CertifiedTraceSequence Δ) : CertifiedTraceSequence (Γ ++ Δ) := by
  induction hΔ with
  | nil => simpa using hΓ
  | @snoc Δ hΔ r hr ih =>
    simpa only [List.append_assoc] using
      CertifiedTraceSequence.snoc ih r (hr.mono fun s hs => List.mem_append_right _ hs)

theorem trace {Γ : List TraceRecord} (hΓ : CertifiedTraceSequence Γ)
    {r : TraceRecord} (hr : r ∈ Γ) :
    Nonempty (BoundedTrace r.fuel r.program r.input r.output) := by
  induction hΓ generalizing r with
  | nil => simp at hr
  | @snoc Γ hΓ s hs ih =>
    rcases List.mem_append.mp hr with h | h
    · exact ih (r := r) h
    · have hrs : r = s := List.mem_singleton.mp h
      subst r
      exact hs.trace fun q hq => ih (r := q) hq

end CertifiedTraceSequence

namespace BoundedTrace

def records : {k : Nat} → {c : Program} → {n v : Nat} →
    BoundedTrace k c n v → List TraceRecord
  | _, _, _, _, .zero k n _ => [⟨k + 1, .zero, n, 0⟩]
  | _, _, _, _, .succ k n _ => [⟨k + 1, .succ, n, n + 1⟩]
  | _, _, _, _, .left k n _ => [⟨k + 1, .left, n, n.unpair.1⟩]
  | _, _, _, _, .right k n _ => [⟨k + 1, .right, n, n.unpair.2⟩]
  | _, _, _, _, .pair k c d n u v _ tc td =>
      tc.records ++ td.records ++ [⟨k + 1, .pair c d, n, Nat.pair u v⟩]
  | _, _, _, _, .comp k c d n u v _ td tc =>
      td.records ++ tc.records ++ [⟨k + 1, .comp c d, n, v⟩]
  | _, _, _, _, .precZero k c d a v _ tc => tc.records ++ [⟨k + 1, .prec c d, Nat.pair a 0, v⟩]
  | _, _, _, _, .precSucc k c d a m u v _ tp td =>
      tp.records ++ td.records ++ [⟨k + 1, .prec c d, Nat.pair a (m + 1), v⟩]
  | _, _, _, _, .searchZero k c a m _ tc => tc.records ++ [⟨k + 1, .rfind' c, Nat.pair a m, m⟩]
  | _, _, _, _, .searchSucc k c a m z v _ tc ts =>
      tc.records ++ ts.records ++ [⟨k + 1, .rfind' c, Nat.pair a m, v⟩]

theorem root_mem_records {k : Nat} {c : Program} {n v : Nat} (t : BoundedTrace k c n v) :
    (⟨k, c, n, v⟩ : TraceRecord) ∈ t.records := by
  cases t <;> simp [records]

theorem records_certified {k : Nat} {c : Program} {n v : Nat} (t : BoundedTrace k c n v) :
    CertifiedTraceSequence t.records := by
  induction t with
  | zero k n hn => exact .snoc .nil _ (.zero k n hn)
  | succ k n hn => exact .snoc .nil _ (.succ k n hn)
  | left k n hn => exact .snoc .nil _ (.left k n hn)
  | right k n hn => exact .snoc .nil _ (.right k n hn)
  | pair k c d n u v hn tc td ihc ihd =>
    exact .snoc (ihc.append ihd) _ (.pair k c d n u v hn
      (List.mem_append_left _ tc.root_mem_records) (List.mem_append_right _ td.root_mem_records))
  | comp k c d n u v hn td tc ihd ihc =>
    exact .snoc (ihd.append ihc) _ (.comp k c d n u v hn
      (List.mem_append_left _ td.root_mem_records) (List.mem_append_right _ tc.root_mem_records))
  | precZero k c d a v hn tc ihc => exact .snoc ihc _ (.precZero k c d a v hn tc.root_mem_records)
  | precSucc k c d a m u v hn tp td ihp ihd =>
    exact .snoc (ihp.append ihd) _ (.precSucc k c d a m u v hn
      (List.mem_append_left _ tp.root_mem_records) (List.mem_append_right _ td.root_mem_records))
  | searchZero k c a m hn tc ihc => exact .snoc ihc _ (.searchZero k c a m hn tc.root_mem_records)
  | searchSucc k c a m z v hn tc ts ihc ihs =>
    exact .snoc (ihc.append ihs) _ (.searchSucc k c a m z v hn
      (List.mem_append_left _ tc.root_mem_records) (List.mem_append_right _ ts.root_mem_records))

end BoundedTrace

theorem W_iff_certified_sequence (e n : Nat) : W e n ↔
    ∃ Γ : List TraceRecord, CertifiedTraceSequence Γ ∧
      ∃ k v, (⟨k, Nat.Partrec.Code.ofNatCode e, n, v⟩ : TraceRecord) ∈ Γ := by
  rw [W_iff_boundedTrace]
  constructor
  · rintro ⟨k, v, ⟨t⟩⟩
    exact ⟨t.records, t.records_certified, k, v, t.root_mem_records⟩
  · rintro ⟨Γ, hΓ, k, v, hr⟩
    exact ⟨k, v, hΓ.trace hr⟩

end Alexander313
