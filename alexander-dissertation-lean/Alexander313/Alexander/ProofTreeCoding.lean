import Alexander313.Alexander.FirstOrderCalculus
import Alexander313.Computability

/-!
# Numeric proof trees and primitive-recursive tree-shape recognition

There are nine leaf rule tags and two recursive rule tags. Labels are natural
numbers, later decoded as the native formulas/terms required by each rule.
The primitive-recursive recognizer below checks this exact finite tree shape,
not the correctness of formula labels or the validity of a derivation.

The native proof-tree encoder/decoder is also constructed, with a literal
round trip. Primitive recursiveness of native formula decoding and native
formula operations is not inferred from these `Encodable` constructions.
-/

namespace Alexander313.FirstOrderCalculus

inductive NumericTree
  | leaf (tag : Fin 9) (payload : Nat)
  | mp (payload : Nat) (p q : NumericTree)
  | generalize (payload : Nat) (p : NumericTree)
  deriving DecidableEq

namespace NumericTree

def code : NumericTree → Nat
  | .leaf tag payload => Nat.pair tag.val payload + 1
  | .mp payload p q => Nat.pair 9 (Nat.pair payload (Nat.pair p.code q.code)) + 1
  | .generalize payload p => Nat.pair 10 (Nat.pair payload p.code) + 1

def decode : Nat → Option NumericTree
  | 0 => none
  | k + 1 =>
    let tag := k.unpair.1
    let payload := k.unpair.2
    if ht : tag < 9 then some (.leaf ⟨tag, ht⟩ payload)
    else if tag = 9 then do
      let p ← decode payload.unpair.2.unpair.1
      let q ← decode payload.unpair.2.unpair.2
      pure (.mp payload.unpair.1 p q)
    else if tag = 10 then do
      let p ← decode payload.unpair.2
      pure (.generalize payload.unpair.1 p)
    else none
termination_by n => n
decreasing_by
  all_goals
    have h₁ := Nat.unpair_right_le k
    have h₂ := Nat.unpair_right_le k.unpair.2
    have h₃ := Nat.unpair_left_le k.unpair.2.unpair.2
    have h₄ := Nat.unpair_right_le k.unpair.2.unpair.2
    omega

@[simp] theorem decode_code (p : NumericTree) : decode p.code = some p := by
  induction p with
  | leaf tag payload => simp [code, decode, tag.isLt, Nat.unpair_pair]
  | mp payload p q ihp ihq => simp [code, decode, Nat.unpair_pair, ihp, ihq]
  | generalize payload p ih => simp [code, decode, Nat.unpair_pair, ih]

def encodable : Encodable NumericTree :=
  Encodable.ofLeftInjection code decode decode_code

theorem code_injective : Function.Injective code := by
  intro p q h
  have hd := congrArg decode h
  exact Option.some.inj (by simpa only [decode_code] using hd)

def isCode : Nat → Bool
  | 0 => false
  | k + 1 =>
    let tag := k.unpair.1
    let payload := k.unpair.2
    cond (decide (tag < 9)) true
      (cond (tag == 9)
        (isCode payload.unpair.2.unpair.1 && isCode payload.unpair.2.unpair.2)
        (cond (tag == 10) (isCode payload.unpair.2) false))
termination_by n => n
decreasing_by
  all_goals
    have h₁ := Nat.unpair_right_le k
    have h₂ := Nat.unpair_right_le k.unpair.2
    have h₃ := Nat.unpair_left_le k.unpair.2.unpair.2
    have h₄ := Nat.unpair_right_le k.unpair.2.unpair.2
    omega

private def recognitionStep (history : List Bool) : Bool :=
  let k := history.length - 1
  let tag := k.unpair.1
  let payload := k.unpair.2
  cond (history.length == 0) false
    (cond (decide (tag < 9)) true
      (cond (tag == 9)
        (history[payload.unpair.2.unpair.1]?.getD false &&
          history[payload.unpair.2.unpair.2]?.getD false)
        (cond (tag == 10) (history[payload.unpair.2]?.getD false) false)))

private theorem recognitionStep_primrec : Primrec recognitionStep := by
  have hk : Primrec (fun h : List Bool => h.length - 1) :=
    Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hc := Primrec.snd.comp (Primrec.unpair.comp hp)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hc)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hc)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have hget (f : List Bool → Nat) (hf : Primrec f) :
      Primrec (fun h : List Bool => h[f h]?.getD false) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hf) (Primrec.const false)
  exact (Primrec.beq.comp Primrec.list_length (Primrec.const 0)).cond
    (Primrec.const false)
    ((Primrec.nat_lt.comp ht (Primrec.const 9)).decide.cond (Primrec.const true)
      ((test 9).cond (Primrec.and.comp (hget _ hl) (hget _ hr))
        ((test 10).cond (hget _ hc) (Primrec.const false))))

theorem isCode_primrec : Primrec isCode := by
  have hg : Primrec₂ (fun (_ : Unit) (h : List Bool) => some (recognitionStep h)) :=
    ((Primrec.option_some.comp recognitionStep_primrec).comp Primrec.snd).to₂
  have htable := Primrec.nat_strong_rec (fun (_ : Unit) n => isCode n) hg
    (by
      intro a n
      cases n with
      | zero => simp [recognitionStep, isCode]
      | succ k =>
        have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
        have hc : k.unpair.2.unpair.2 < k + 1 :=
          lt_of_le_of_lt (Nat.unpair_right_le _) hp
        have hl : k.unpair.2.unpair.2.unpair.1 < k + 1 :=
          lt_of_le_of_lt (Nat.unpair_left_le _) hc
        have hr : k.unpair.2.unpair.2.unpair.2 < k + 1 :=
          lt_of_le_of_lt (Nat.unpair_right_le _) hc
        simp [recognitionStep, isCode, hp, hc, hl, hr])
  exact htable.comp (Primrec.const ()) Primrec.id

@[simp] theorem isCode_code (p : NumericTree) : isCode p.code = true := by
  induction p <;> simp_all [code, isCode, Nat.unpair_pair, Fin.isLt]

theorem isCode_sound (n : Nat) : isCode n = true → ∃ p : NumericTree, p.code = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [isCode]
    | succ k =>
      intro hn
      let tag := k.unpair.1
      let payload := k.unpair.2
      have hp : payload < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hc : payload.unpair.2 < k + 1 :=
        lt_of_le_of_lt (Nat.unpair_right_le _) hp
      have hl : payload.unpair.2.unpair.1 < k + 1 :=
        lt_of_le_of_lt (Nat.unpair_left_le _) hc
      have hr : payload.unpair.2.unpair.2 < k + 1 :=
        lt_of_le_of_lt (Nat.unpair_right_le _) hc
      have hk : k = Nat.pair tag payload := (Nat.pair_unpair k).symm
      by_cases ht : tag < 9
      · refine ⟨.leaf ⟨tag, ht⟩ payload, ?_⟩
        rw [hk]
        rfl
      by_cases h9 : tag = 9
      · have hchildren : isCode payload.unpair.2.unpair.1 = true ∧
            isCode payload.unpair.2.unpair.2 = true := by
          simpa [isCode, tag, payload, ht, h9] using hn
        obtain ⟨p, hpcode⟩ := ih _ hl hchildren.1
        obtain ⟨q, hqcode⟩ := ih _ hr hchildren.2
        refine ⟨.mp payload.unpair.1 p q, ?_⟩
        rw [hk, h9]
        simp only [code, hpcode, hqcode, Nat.pair_unpair]
      by_cases h10 : tag = 10
      · have hchild : isCode payload.unpair.2 = true := by
          simpa [isCode, tag, payload, ht, h9, h10] using hn
        obtain ⟨p, hpcode⟩ := ih _ hc hchild
        refine ⟨.generalize payload.unpair.1 p, ?_⟩
        rw [hk, h10]
        simp only [code, hpcode, Nat.pair_unpair]
      simp [isCode, tag, payload, ht, h9, h10] at hn

theorem isCode_iff (n : Nat) : isCode n = true ↔ ∃ p : NumericTree, p.code = n :=
  ⟨isCode_sound n, fun ⟨p, hp⟩ => hp ▸ isCode_code p⟩

end NumericTree

universe u v

variable {L : FirstOrder.Language.{u, v}}
variable [Encodable (L.Formula Nat)] [Encodable L.Sentence] [Encodable (L.Term Nat)]

def ProofTree.numericTree : ProofTree L → NumericTree
  | .assumption σ => .leaf 0 (Encodable.encode σ)
  | .k φ ψ => .leaf 1 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ))
  | .s φ ψ χ => .leaf 2 (Nat.pair (Encodable.encode φ)
      (Nat.pair (Encodable.encode ψ) (Encodable.encode χ)))
  | .classical φ ψ => .leaf 3 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ))
  | .allElim x t φ => .leaf 4 (Nat.pair x
      (Nat.pair (Encodable.encode t) (Encodable.encode φ)))
  | .allDist x φ ψ => .leaf 5 (Nat.pair x
      (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)))
  | .vacuous x φ => .leaf 6 (Nat.pair x (Encodable.encode φ))
  | .eqRefl t => .leaf 7 (Encodable.encode t)
  | .eqSubst x t u φ => .leaf 8 (Nat.pair x (Nat.pair (Encodable.encode t)
      (Nat.pair (Encodable.encode u) (Encodable.encode φ))))
  | .mp φ ψ p q => .mp (Nat.pair (Encodable.encode φ) (Encodable.encode ψ))
      p.numericTree q.numericTree
  | .generalize x φ p => .generalize (Nat.pair x (Encodable.encode φ)) p.numericTree

def NumericTree.toNative : NumericTree → Option (ProofTree L)
  | .leaf tag payload => match tag.val with
    | 0 => do
      let σ ← Encodable.decode (α := L.Sentence) payload
      pure (.assumption σ)
    | 1 => do
      let φ ← Encodable.decode (α := L.Formula Nat) payload.unpair.1
      let ψ ← Encodable.decode (α := L.Formula Nat) payload.unpair.2
      pure (.k φ ψ)
    | 2 => do
      let φ ← Encodable.decode (α := L.Formula Nat) payload.unpair.1
      let ψ ← Encodable.decode (α := L.Formula Nat) payload.unpair.2.unpair.1
      let χ ← Encodable.decode (α := L.Formula Nat) payload.unpair.2.unpair.2
      pure (.s φ ψ χ)
    | 3 => do
      let φ ← Encodable.decode (α := L.Formula Nat) payload.unpair.1
      let ψ ← Encodable.decode (α := L.Formula Nat) payload.unpair.2
      pure (.classical φ ψ)
    | 4 => (Encodable.decode (α := L.Term Nat) payload.unpair.2.unpair.1).bind fun t => do
      let φ ← Encodable.decode (α := L.Formula Nat) payload.unpair.2.unpair.2
      pure (.allElim payload.unpair.1 t φ)
    | 5 => do
      let φ ← Encodable.decode (α := L.Formula Nat) payload.unpair.2.unpair.1
      let ψ ← Encodable.decode (α := L.Formula Nat) payload.unpair.2.unpair.2
      pure (.allDist payload.unpair.1 φ ψ)
    | 6 => do
      let φ ← Encodable.decode (α := L.Formula Nat) payload.unpair.2
      pure (.vacuous payload.unpair.1 φ)
    | 7 => (Encodable.decode (α := L.Term Nat) payload).map ProofTree.eqRefl
    | 8 => (Encodable.decode (α := L.Term Nat) payload.unpair.2.unpair.1).bind fun t =>
      (Encodable.decode (α := L.Term Nat) payload.unpair.2.unpair.2.unpair.1).bind fun u => do
      let φ ← Encodable.decode (α := L.Formula Nat) payload.unpair.2.unpair.2.unpair.2
      pure (.eqSubst payload.unpair.1 t u φ)
    | _ => none
  | .mp payload p q => do
    let φ ← Encodable.decode (α := L.Formula Nat) payload.unpair.1
    let ψ ← Encodable.decode (α := L.Formula Nat) payload.unpair.2
    let p' ← p.toNative
    let q' ← q.toNative
    pure (.mp φ ψ p' q')
  | .generalize payload p => do
    let φ ← Encodable.decode (α := L.Formula Nat) payload.unpair.2
    let p' ← p.toNative
    pure (.generalize payload.unpair.1 φ p')

@[simp] theorem ProofTree.toNative_numericTree (p : ProofTree L) :
    p.numericTree.toNative = some p := by
  induction p <;> simp_all [ProofTree.numericTree, NumericTree.toNative,
    Nat.unpair_pair, Encodable.encodek]

def proofTreeEncodable : Encodable (ProofTree L) :=
  Encodable.ofLeftInjection (fun p : ProofTree L => p.numericTree.code)
    (fun n => (NumericTree.decode n).bind NumericTree.toNative)
    (fun p => by simp)

variable [DecidableEq (L.Formula Nat)]

/-- The complete syntax computation on numeric inputs. Its primitive-recursive
    proof still requires the native label decoder and formula-operation laws. -/
def checkCode (accept : L.Sentence → Bool) (n : Nat) : Option (L.Formula Nat) :=
  (NumericTree.decode n).bind fun raw => raw.toNative.bind (check accept)

@[simp] theorem checkCode_numericTree (accept : L.Sentence → Bool) (p : ProofTree L) :
    checkCode accept p.numericTree.code = check accept p := by
  simp [checkCode]

theorem checkCode_checked {accept : L.Sentence → Bool} {n : Nat}
    {φ : L.Formula Nat} (h : checkCode accept n = some φ) : CheckedProof accept φ := by
  obtain ⟨raw, _, hraw⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨p, _, hp⟩ := Option.bind_eq_some_iff.mp hraw
  exact ⟨p, hp⟩

theorem exists_checkCode_iff (accept : L.Sentence → Bool) (φ : L.Formula Nat) :
    (∃ n, checkCode accept n = some φ) ↔ CheckedProof accept φ := by
  constructor
  · rintro ⟨n, hn⟩
    exact checkCode_checked hn
  · rintro ⟨p, hp⟩
    exact ⟨p.numericTree.code, by simpa only [checkCode_numericTree] using hp⟩

end Alexander313.FirstOrderCalculus
