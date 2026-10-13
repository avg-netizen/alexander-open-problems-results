import Alexander313.Wilken.RelativeTerms
import Alexander313.Computability

/-!
# Literal coding of raw relative terms

This codes the existing `RelativeTerm Nat` syntax, with tags 0, 1 and 2 for
parameters, sums and theta terms. The decoder and Boolean recognizer recurse
only on smaller literal codes; the primitive-recursion proof uses a finite
table of earlier answers. No ordinal parameter domain, sort restriction,
additive normal form, semantic equality or ordinal comparison is inferred
from membership in this raw syntax image.
-/

namespace Alexander313.Wilken.RelativeTerm

def code : RelativeTerm Nat → Nat
  | .parameter p => Nat.succ (Nat.pair 0 p)
  | .sum a b => Nat.succ (Nat.pair 1 (Nat.pair a.code b.code))
  | .theta k a => Nat.succ (Nat.pair 2 (Nat.pair k a.code))

@[simp] theorem code_parameter (p : Nat) :
    code (.parameter p) = Nat.succ (Nat.pair 0 p) := rfl

@[simp] theorem code_sum (a b : RelativeTerm Nat) :
    code (.sum a b) = Nat.succ (Nat.pair 1 (Nat.pair a.code b.code)) := rfl

@[simp] theorem code_theta (k : Nat) (a : RelativeTerm Nat) :
    code (.theta k a) = Nat.succ (Nat.pair 2 (Nat.pair k a.code)) := rfl

def decode : Nat → Option (RelativeTerm Nat)
  | 0 => none
  | n + 1 =>
    let tag := n.unpair.1
    let p := n.unpair.2
    if tag = 0 then some (.parameter p)
    else if tag = 1 then do
      let a ← decode p.unpair.1
      let b ← decode p.unpair.2
      pure (.sum a b)
    else if tag = 2 then do
      let a ← decode p.unpair.2
      pure (.theta p.unpair.1 a)
    else none
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le n
    have hl := Nat.unpair_left_le n.unpair.2
    have hr := Nat.unpair_right_le n.unpair.2
    omega

@[simp] theorem decode_code (t : RelativeTerm Nat) : decode t.code = some t := by
  induction t <;> simp_all [code, decode, Nat.unpair_pair]

theorem code_injective : Function.Injective code := by
  intro a b h
  have hd := congrArg decode h
  exact Option.some.inj (by simpa only [decode_code] using hd)

@[simp] theorem code_eq_iff (a b : RelativeTerm Nat) : a.code = b.code ↔ a = b :=
  code_injective.eq_iff

theorem decode_sound (n : Nat) (t : RelativeTerm Nat) :
    decode n = some t → t.code = n := by
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
    cases n with
    | zero => simp [decode]
    | succ k =>
      intro hn
      let tag := k.unpair.1
      let p := k.unpair.2
      have hp : p < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : p.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le p) hp
      have hr : p.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le p) hp
      have hk : k = Nat.pair tag p := (Nat.pair_unpair k).symm
      by_cases h0 : tag = 0
      · have ht : parameter p = t := by simpa [decode, tag, p, h0] using hn
        rw [← ht, code, hk, h0]
      by_cases h1 : tag = 1
      · have hs : (do
            let a ← decode p.unpair.1
            let b ← decode p.unpair.2
            pure (sum a b)) = some t := by
          simpa [decode, tag, p, h0, h1] using hn
        cases ha : decode p.unpair.1 with
        | none => simp [ha] at hs
        | some a =>
          cases hb : decode p.unpair.2 with
          | none => simp [ha, hb] at hs
          | some b =>
            have ht : sum a b = t := by simpa [ha, hb] using hs
            have hca := ih _ hl a ha
            have hcb := ih _ hr b hb
            rw [← ht, code, hca, hcb, Nat.pair_unpair, hk, h1]
      by_cases h2 : tag = 2
      · have hs : (do
            let a ← decode p.unpair.2
            pure (theta p.unpair.1 a)) = some t := by
          simpa [decode, tag, p, h0, h1, h2] using hn
        cases ha : decode p.unpair.2 with
        | none => simp [ha] at hs
        | some a =>
          have ht : theta p.unpair.1 a = t := by simpa [ha] using hs
          have hca := ih _ hr a ha
          rw [← ht, code, hca, Nat.pair_unpair, hk, h2]
      simp [decode, tag, p, h0, h1, h2] at hn

theorem decode_eq_some_iff (n : Nat) (t : RelativeTerm Nat) :
    decode n = some t ↔ t.code = n :=
  ⟨decode_sound n t, fun ht => ht ▸ decode_code t⟩

def isCode : Nat → Bool
  | 0 => false
  | n + 1 =>
    let tag := n.unpair.1
    let p := n.unpair.2
    cond (tag == 0) true
      (cond (tag == 1) (isCode p.unpair.1 && isCode p.unpair.2)
        (cond (tag == 2) (isCode p.unpair.2) false))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le n
    have hl := Nat.unpair_left_le n.unpair.2
    have hr := Nat.unpair_right_le n.unpair.2
    omega

private def recognitionStep (h : List Bool) : Bool :=
  let n := h.length - 1
  let tag := n.unpair.1
  let p := n.unpair.2
  cond (h.length == 0) false
    (cond (tag == 0) true
      (cond (tag == 1) (h[p.unpair.1]?.getD false && h[p.unpair.2]?.getD false)
        (cond (tag == 2) (h[p.unpair.2]?.getD false) false)))

private theorem recognitionStep_primrec : Primrec recognitionStep := by
  have hn : Primrec (fun h : List Bool => h.length - 1) :=
    Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hn)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hn)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (n : Nat) := Primrec.beq.comp ht (Primrec.const n)
  have get (f : List Bool → Nat) (hf : Primrec f) :
      Primrec (fun h : List Bool => h[f h]?.getD false) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hf) (Primrec.const false)
  exact (Primrec.beq.comp Primrec.list_length (Primrec.const 0)).cond
    (Primrec.const false)
    ((test 0).cond (Primrec.const true)
      ((test 1).cond (Primrec.and.comp (get _ hl) (get _ hr))
        ((test 2).cond (get _ hr) (Primrec.const false))))

theorem isCode_primrec : Primrec isCode := by
  have hg : Primrec₂ (fun (_ : Unit) (h : List Bool) => some (recognitionStep h)) :=
    ((Primrec.option_some.comp recognitionStep_primrec).comp Primrec.snd).to₂
  have htable := Primrec.nat_strong_rec (fun (_ : Unit) n => isCode n) hg (by
    intro a n
    cases n with
    | zero => simp [recognitionStep, isCode]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [recognitionStep, isCode, hp, hl, hr])
  exact htable.comp (Primrec.const ()) Primrec.id

@[simp] theorem isCode_code (t : RelativeTerm Nat) : isCode t.code = true := by
  induction t <;> simp_all [code, isCode, Nat.unpair_pair]

theorem isCode_sound (n : Nat) :
    isCode n = true → ∃ t : RelativeTerm Nat, t.code = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [isCode]
    | succ k =>
      intro hn
      let tag := k.unpair.1
      let p := k.unpair.2
      have hp : p < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : p.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le p) hp
      have hr : p.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le p) hp
      have hk : k = Nat.pair tag p := (Nat.pair_unpair k).symm
      by_cases h0 : tag = 0
      · refine ⟨.parameter p, ?_⟩
        rw [hk, h0]
        rfl
      by_cases h1 : tag = 1
      · have hc : isCode p.unpair.1 = true ∧ isCode p.unpair.2 = true := by
          simpa [isCode, tag, p, h0, h1] using hn
        obtain ⟨a, ha⟩ := ih _ hl hc.1
        obtain ⟨b, hb⟩ := ih _ hr hc.2
        refine ⟨.sum a b, ?_⟩
        rw [hk, h1]
        simp only [code, ha, hb, Nat.pair_unpair]
      by_cases h2 : tag = 2
      · have hc : isCode p.unpair.2 = true := by
          simpa [isCode, tag, p, h0, h1, h2] using hn
        obtain ⟨a, ha⟩ := ih _ hr hc
        refine ⟨.theta p.unpair.1 a, ?_⟩
        rw [hk, h2]
        simp only [code, ha, Nat.pair_unpair]
      simp [isCode, tag, p, h0, h1, h2] at hn

theorem isCode_iff (n : Nat) :
    isCode n = true ↔ ∃ t : RelativeTerm Nat, t.code = n :=
  ⟨isCode_sound n, fun ⟨t, ht⟩ => ht ▸ isCode_code t⟩

theorem decode_eq_none_iff (n : Nat) : decode n = none ↔ isCode n = false := by
  constructor
  · intro hd
    cases hc : isCode n with
    | false => rfl
    | true =>
      obtain ⟨t, ht⟩ := isCode_sound n hc
      have hs := decode_code t
      rw [ht, hd] at hs
      cases hs
  · intro hc
    cases hd : decode n with
    | none => rfl
    | some t =>
      have ht := decode_sound n t hd
      have hs := isCode_code t
      rw [ht, hc] at hs
      cases hs

def literalCodeEquiv : RelativeTerm Nat ≃ {n : Nat // isCode n = true} where
  toFun := fun t => ⟨t.code, isCode_code t⟩
  invFun := fun n => (decode n.val).getD (.parameter 0)
  left_inv := fun t => by simp only [decode_code, Option.getD_some]
  right_inv := fun n => by
    obtain ⟨t, ht⟩ := isCode_sound n.val n.property
    apply Subtype.ext
    simp only [← ht, decode_code, Option.getD_some]

instance literalPrimcodable : Primcodable (RelativeTerm Nat) := by
  letI : Primcodable {n : Nat // isCode n = true} :=
    Primcodable.subtype (Primrec.eq.comp isCode_primrec (Primrec.const true))
  exact Primcodable.ofEquiv {n : Nat // isCode n = true} literalCodeEquiv

@[simp] theorem encode_eq_code (t : RelativeTerm Nat) : Encodable.encode t = t.code := rfl

theorem code_primrec : Primrec code := by
  exact (Primrec.encode : Primrec (Encodable.encode (α := RelativeTerm Nat))).of_eq
    (fun _ => rfl)

theorem decode_eq_decode₂ (n : Nat) :
    decode n = Encodable.decode₂ (RelativeTerm Nat) n := by
  cases hd : decode n with
  | none =>
    cases he : Encodable.decode₂ (RelativeTerm Nat) n with
    | none => rfl
    | some t =>
      have ht : t.code = n := by
        simpa only [encode_eq_code] using
          (Encodable.decode₂_eq_some (n := n) (a := t)).mp he
      have hs := decode_code t
      rw [ht, hd] at hs
      cases hs
  | some t =>
    have ht := decode_sound n t hd
    have he : Encodable.decode₂ (RelativeTerm Nat) n = some t := by
      apply (Encodable.decode₂_eq_some (n := n) (a := t)).mpr
      simpa only [encode_eq_code] using ht
    exact he.symm

theorem decode_primrec : Primrec decode := by
  have heq : decode = Encodable.decode₂ (RelativeTerm Nat) := funext decode_eq_decode₂
  rw [heq]
  exact Primrec.decode₂

theorem parameter_primrec : Primrec (parameter : Nat → RelativeTerm Nat) := by
  apply Primrec.encode_iff.1
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id)).of_eq
    (fun _ => rfl)

theorem sum_primrec : Primrec₂ (sum : RelativeTerm Nat → RelativeTerm Nat → RelativeTerm Nat) := by
  apply Primrec.encode_iff.1
  have hp := Primrec₂.natPair.comp (code_primrec.comp Primrec.fst)
    (code_primrec.comp Primrec.snd)
  simpa only [encode_eq_code, code_sum] using
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) hp)

theorem theta_primrec : Primrec₂ (theta : Nat → RelativeTerm Nat → RelativeTerm Nat) := by
  apply Primrec.encode_iff.1
  have hp := Primrec₂.natPair.comp Primrec.fst (code_primrec.comp Primrec.snd)
  simpa only [encode_eq_code, code_theta] using
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2) hp)

namespace ValueFold

variable {α β : Type} [Primcodable α] [Primcodable β]

/-- A raw-code value fold. Invalid root tags return the supplied base value.
    On a valid code it processes the actual parameter, both sum arguments,
    and the actual theta index. -/
def code (parameterOp : α → Nat → β) (sumOp : β → β → β)
    (thetaOp : α → Nat → β → β) (base : β) (a : α) : Nat → β
  | 0 => base
  | n + 1 =>
    let tag := n.unpair.1
    let p := n.unpair.2
    cond (tag == 0) (parameterOp a p)
      (cond (tag == 1)
        (sumOp (code parameterOp sumOp thetaOp base a p.unpair.1)
          (code parameterOp sumOp thetaOp base a p.unpair.2))
        (cond (tag == 2)
          (thetaOp a p.unpair.1 (code parameterOp sumOp thetaOp base a p.unpair.2)) base))
termination_by n => n
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le n
    have hl := Nat.unpair_left_le n.unpair.2
    have hr := Nat.unpair_right_le n.unpair.2
    omega

private def step (parameterOp : α → Nat → β) (sumOp : β → β → β)
    (thetaOp : α → Nat → β → β) (base : β) (a : α) (h : List β) : β :=
  let n := h.length - 1
  let tag := n.unpair.1
  let p := n.unpair.2
  cond (h.length == 0) base
    (cond (tag == 0) (parameterOp a p)
      (cond (tag == 1)
        (sumOp (h[p.unpair.1]?.getD base) (h[p.unpair.2]?.getD base))
        (cond (tag == 2) (thetaOp a p.unpair.1 (h[p.unpair.2]?.getD base)) base)))

private theorem step_primrec (parameterOp : α → Nat → β) (sumOp : β → β → β)
    (thetaOp : α → Nat → β → β) (base : β)
    (hp : Primrec₂ parameterOp) (hs : Primrec₂ sumOp)
    (ht : Primrec (fun p : α × (Nat × β) => thetaOp p.1 p.2.1 p.2.2)) :
    Primrec₂ (step parameterOp sumOp thetaOp base) := by
  have hn : Primrec (fun p : α × List β => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have htag := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hpay := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have test (n : Nat) := Primrec.beq.comp htag (Primrec.const n)
  have get (f : α × List β → Nat) (hf : Primrec f) :
      Primrec (fun p : α × List β => p.2[f p]?.getD base) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hf) (Primrec.const base)
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const base)
    ((test 0).cond (hp.comp Primrec.fst hpay)
      ((test 1).cond (hs.comp (get _ hl) (get _ hr))
        ((test 2).cond (ht.comp (Primrec.fst.pair (hl.pair (get _ hr))))
          (Primrec.const base))))).to₂

theorem code_primrec (parameterOp : α → Nat → β) (sumOp : β → β → β)
    (thetaOp : α → Nat → β → β) (base : β)
    (hp : Primrec₂ parameterOp) (hs : Primrec₂ sumOp)
    (ht : Primrec (fun p : α × (Nat × β) => thetaOp p.1 p.2.1 p.2.2)) :
    Primrec₂ (code parameterOp sumOp thetaOp base) := by
  have hg := Primrec.option_some.comp₂ (step_primrec parameterOp sumOp thetaOp base hp hs ht)
  exact Primrec.nat_strong_rec (code parameterOp sumOp thetaOp base) hg (by
    intro a n
    cases n with
    | zero => simp [step, code]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [step, code, hp, hl, hr])

def term (parameterOp : α → Nat → β) (sumOp : β → β → β)
    (thetaOp : α → Nat → β → β) (a : α) : RelativeTerm Nat → β
  | .parameter p => parameterOp a p
  | .sum s t => sumOp (term parameterOp sumOp thetaOp a s) (term parameterOp sumOp thetaOp a t)
  | .theta k t => thetaOp a k (term parameterOp sumOp thetaOp a t)

@[simp] theorem code_term (parameterOp : α → Nat → β) (sumOp : β → β → β)
    (thetaOp : α → Nat → β → β) (base : β) (a : α) (t : RelativeTerm Nat) :
    code parameterOp sumOp thetaOp base a t.code = term parameterOp sumOp thetaOp a t := by
  induction t <;> simp_all [code, term, RelativeTerm.code, Nat.unpair_pair]

theorem term_primrec (parameterOp : α → Nat → β) (sumOp : β → β → β)
    (thetaOp : α → Nat → β → β) (base : β)
    (hp : Primrec₂ parameterOp) (hs : Primrec₂ sumOp)
    (ht : Primrec (fun p : α × (Nat × β) => thetaOp p.1 p.2.1 p.2.2)) :
    Primrec₂ (term parameterOp sumOp thetaOp) := by
  have hf := (code_primrec parameterOp sumOp thetaOp base hp hs ht).comp Primrec.fst
    (RelativeTerm.code_primrec.comp Primrec.snd)
  exact hf.of_eq (fun _ => code_term _ _ _ _ _ _)

end ValueFold

def sizeCode (n : Nat) : Nat :=
  ValueFold.code (fun (_ : Unit) _ => 1) (fun a b => a + b + 1)
    (fun _ _ a => a + 1) 0 () n

theorem sizeCode_primrec : Primrec sizeCode := by
  have hs : Primrec₂ (fun a b : Nat => a + b + 1) :=
    (Primrec.succ.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd)).to₂
  have ht : Primrec (fun p : Unit × (Nat × Nat) => p.2.2 + 1) :=
    Primrec.succ.comp (Primrec.snd.comp Primrec.snd)
  exact (ValueFold.code_primrec _ _ _ _ (Primrec.const 1).to₂ hs ht).comp
    (Primrec.const ()) Primrec.id

@[simp] theorem sizeCode_code (t : RelativeTerm Nat) : sizeCode t.code = t.size := by
  unfold sizeCode
  rw [ValueFold.code_term]
  induction t <;> simp_all [ValueFold.term, size]

theorem size_primrec : Primrec (size (Parameter := Nat)) := by
  simpa only [sizeCode_code] using sizeCode_primrec.comp code_primrec

def heightCode (n : Nat) : Nat :=
  ValueFold.code (fun (_ : Unit) _ => 0) max
    (fun _ k a => max (k + 1) a) 0 () n

theorem heightCode_primrec : Primrec heightCode := by
  have ht : Primrec (fun p : Unit × (Nat × Nat) => max (p.2.1 + 1) p.2.2) :=
    Primrec.nat_max.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact (ValueFold.code_primrec _ _ _ _ (Primrec.const 0).to₂ Primrec.nat_max ht).comp
    (Primrec.const ()) Primrec.id

@[simp] theorem heightCode_code (t : RelativeTerm Nat) : heightCode t.code = t.height := by
  unfold heightCode
  rw [ValueFold.code_term]
  induction t <;> simp_all [ValueFold.term, height]

theorem height_primrec : Primrec (height (Parameter := Nat)) := by
  simpa only [heightCode_code] using heightCode_primrec.comp code_primrec

/-- Theta-index occurrences in written order; duplicates are retained. -/
def indexList : RelativeTerm Nat → List Nat
  | .parameter _ => []
  | .sum a b => a.indexList ++ b.indexList
  | .theta k a => k :: a.indexList

def indexListCode (n : Nat) : List Nat :=
  ValueFold.code (fun (_ : Unit) _ => []) List.append (fun _ k xs => k :: xs) [] () n

theorem indexListCode_primrec : Primrec indexListCode := by
  have ht : Primrec (fun p : Unit × (Nat × List Nat) => p.2.1 :: p.2.2) :=
    Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (ValueFold.code_primrec _ _ _ _ (Primrec.const []).to₂ Primrec.list_append ht).comp
    (Primrec.const ()) Primrec.id

@[simp] theorem indexListCode_code (t : RelativeTerm Nat) :
    indexListCode t.code = t.indexList := by
  unfold indexListCode
  rw [ValueFold.code_term]
  induction t <;> simp_all [ValueFold.term, indexList]

theorem indexList_primrec : Primrec indexList := by
  simpa only [indexListCode_code] using indexListCode_primrec.comp code_primrec

@[simp] theorem indexList_toFinset (t : RelativeTerm Nat) : t.indexList.toFinset = t.indices := by
  induction t <;> simp_all [indexList, indices]

theorem mem_indexList_iff (k : Nat) (t : RelativeTerm Nat) :
    k ∈ t.indexList ↔ k ∈ t.indices := by
  rw [← indexList_toFinset]
  exact List.mem_toFinset.symm

/-- Parameter occurrences in written order; no semantic admissibility test
    is performed on their natural-number payloads. -/
def parameterList : RelativeTerm Nat → List Nat
  | .parameter p => [p]
  | .sum a b => a.parameterList ++ b.parameterList
  | .theta _ a => a.parameterList

def parameterListCode (n : Nat) : List Nat :=
  ValueFold.code (fun (_ : Unit) p => [p]) List.append (fun _ _ xs => xs) [] () n

theorem parameterListCode_primrec : Primrec parameterListCode := by
  have hp : Primrec₂ (fun (_ : Unit) (p : Nat) => [p]) :=
    (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to₂
  have ht : Primrec (fun p : Unit × (Nat × List Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact (ValueFold.code_primrec _ _ _ _ hp Primrec.list_append ht).comp
    (Primrec.const ()) Primrec.id

@[simp] theorem parameterListCode_code (t : RelativeTerm Nat) :
    parameterListCode t.code = t.parameterList := by
  unfold parameterListCode
  rw [ValueFold.code_term]
  induction t <;> simp_all [ValueFold.term, parameterList]

theorem parameterList_primrec : Primrec parameterList := by
  simpa only [parameterListCode_code] using parameterListCode_primrec.comp code_primrec

@[simp] theorem parameterList_toFinset (t : RelativeTerm Nat) :
    t.parameterList.toFinset = t.parameters := by
  induction t <;> simp_all [parameterList, parameters]

theorem mem_parameterList_iff (p : Nat) (t : RelativeTerm Nat) :
    p ∈ t.parameterList ↔ p ∈ t.parameters := by
  rw [← parameterList_toFinset]
  exact List.mem_toFinset.symm

def mapParameters {P Q : Type} (f : P → Q) : RelativeTerm P → RelativeTerm Q
  | .parameter p => .parameter (f p)
  | .sum a b => .sum (a.mapParameters f) (b.mapParameters f)
  | .theta k a => .theta k (a.mapParameters f)

@[simp] theorem size_mapParameters {P Q : Type} (f : P → Q) (t : RelativeTerm P) :
    (t.mapParameters f).size = t.size := by
  induction t <;> simp_all [mapParameters, size]

@[simp] theorem height_mapParameters {P Q : Type} (f : P → Q) (t : RelativeTerm P) :
    (t.mapParameters f).height = t.height := by
  induction t <;> simp_all [mapParameters, height]

@[simp] theorem indices_mapParameters {P Q : Type} (f : P → Q) (t : RelativeTerm P) :
    (t.mapParameters f).indices = t.indices := by
  induction t <;> simp_all [mapParameters, indices]

theorem mapParameters_primrec {α : Type} [Primcodable α]
    (f : α → Nat → Nat) (hf : Primrec₂ f) :
    Primrec₂ (fun a (t : RelativeTerm Nat) => t.mapParameters (f a)) := by
  have hp : Primrec₂ (fun a p => parameter (f a p)) := parameter_primrec.comp₂ hf
  have ht : Primrec (fun p : α × (Nat × RelativeTerm Nat) => theta p.2.1 p.2.2) :=
    theta_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hfold := ValueFold.term_primrec (fun a p => parameter (f a p)) sum
    (fun _ k t => theta k t) (parameter 0) hp sum_primrec ht
  have heq (a : α) (t : RelativeTerm Nat) :
      ValueFold.term (fun a p => parameter (f a p)) sum (fun _ k t => theta k t) a t =
        t.mapParameters (f a) := by
    induction t <;> simp_all [ValueFold.term, mapParameters]
  exact hfold.of_eq (fun _ _ => heq _ _)

end Alexander313.Wilken.RelativeTerm
