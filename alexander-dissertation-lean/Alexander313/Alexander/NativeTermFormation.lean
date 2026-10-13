import Alexander313.Alexander.NativeRelationCoding

/-!
# Primitive-recursive native arithmetic term labels

Native terms use the actual Δ arithmetic function symbols. Their literal
codes use the source term tags, with a variable payload `(0, x)` for a free
variable and `(1, i)` for a bound variable. The latter is accepted exactly
when `i` is in the displayed de Bruijn context. The code recognizer has a
primitive-recursive finite-history implementation; both directions of its
exact-image theorem are proved below.
-/

namespace Alexander313.Delta.NativeTerm

abbrev Syntax (n : Nat) := (language Nat).Term (Nat ⊕ Fin n)

def variableCode {n : Nat} : Nat ⊕ Fin n → Nat
  | .inl x => Nat.pair 0 x
  | .inr i => Nat.pair 1 i.val

def variableIsCode (n p : Nat) : Bool :=
  (p.unpair.1 == 0) || ((p.unpair.1 == 1) && decide (p.unpair.2 < n))

theorem variableIsCode_primrec : Primrec₂ variableIsCode := by
  have ht : Primrec (fun q : Nat × Nat => q.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hp : Primrec (fun q : Nat × Nat => q.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  exact (Primrec.or.comp (Primrec.beq.comp ht (Primrec.const 0))
    (Primrec.and.comp (Primrec.beq.comp ht (Primrec.const 1))
      (Primrec.nat_lt.comp hp Primrec.fst).decide)).to₂

@[simp] theorem variableIsCode_code {n : Nat} (v : Nat ⊕ Fin n) :
    variableIsCode n (variableCode v) = true := by
  cases v <;> simp [variableCode, variableIsCode, Nat.unpair_pair]

theorem variableIsCode_sound (n p : Nat) (h : variableIsCode n p = true) :
    ∃ v : Nat ⊕ Fin n, variableCode v = p := by
  have hp : Nat.pair p.unpair.1 p.unpair.2 = p := Nat.pair_unpair p
  rcases Bool.or_eq_true_iff.mp h with h0 | h1
  · have ht : p.unpair.1 = 0 := by simpa using h0
    exact ⟨.inl p.unpair.2, by simpa only [variableCode, ht] using hp⟩
  · have hs := Bool.and_eq_true_iff.mp h1
    have ht : p.unpair.1 = 1 := by simpa using hs.1
    have hn : p.unpair.2 < n := by simpa using hs.2
    exact ⟨.inr ⟨p.unpair.2, hn⟩, by simpa only [variableCode, ht] using hp⟩

def decodeVariable (n p : Nat) : Option (Nat ⊕ Fin n) :=
  if p.unpair.1 = 0 then some (.inl p.unpair.2)
  else if p.unpair.1 = 1 then
    if h : p.unpair.2 < n then some (.inr ⟨p.unpair.2, h⟩) else none
  else none

@[simp] theorem decodeVariable_code {n : Nat} (v : Nat ⊕ Fin n) :
    decodeVariable n (variableCode v) = some v := by
  cases v <;> simp [decodeVariable, variableCode, Nat.unpair_pair]

def toLiteral {n : Nat} : Syntax n → Term
  | .var v => .var (variableCode v)
  | .func .zero _ => .zero
  | .func .succ ts => .succ (toLiteral (ts 0))
  | .func .add ts => .add (toLiteral (ts 0)) (toLiteral (ts 1))
  | .func .mul ts => .mul (toLiteral (ts 0)) (toLiteral (ts 1))

def ofLiteral (n : Nat) : Term → Option (Syntax n)
  | .var p => (decodeVariable n p).map .var
  | .zero => some (.func .zero Fin.elim0)
  | .succ t => (ofLiteral n t).map ((FirstOrder.Language.Functions.apply₁ (L := language Nat) ArithmeticSymbol.succ))
  | .add t u => do
      let t' ← ofLiteral n t
      let u' ← ofLiteral n u
      pure ((FirstOrder.Language.Functions.apply₂ (L := language Nat) ArithmeticSymbol.add) t' u')
  | .mul t u => do
      let t' ← ofLiteral n t
      let u' ← ofLiteral n u
      pure ((FirstOrder.Language.Functions.apply₂ (L := language Nat) ArithmeticSymbol.mul) t' u')

@[simp] theorem ofLiteral_toLiteral {n : Nat} (t : Syntax n) :
    ofLiteral n (toLiteral t) = some t := by
  induction t with
  | var v => simp [toLiteral, ofLiteral]
  | func f ts ih =>
    cases f with
    | zero =>
      simp only [toLiteral, ofLiteral]
      apply congrArg (fun u : Fin 0 → Syntax n => some (.func .zero u : Syntax n))
      funext i
      exact Fin.elim0 i
    | succ =>
      simp only [toLiteral, ofLiteral, ih, Option.map_some,
        FirstOrder.Language.Functions.apply₁]
      apply congrArg (fun u : Fin 1 → Syntax n => some (.func .succ u : Syntax n))
      funext i
      fin_cases i
      rfl
    | add =>
      simp only [toLiteral, ofLiteral, ih, Option.bind_some,
        FirstOrder.Language.Functions.apply₂]
      apply congrArg (fun u : Fin 2 → Syntax n => some (.func .add u : Syntax n))
      funext i
      fin_cases i <;> rfl
    | mul =>
      simp only [toLiteral, ofLiteral, ih, Option.bind_some,
        FirstOrder.Language.Functions.apply₂]
      apply congrArg (fun u : Fin 2 → Syntax n => some (.func .mul u : Syntax n))
      funext i
      fin_cases i <;> rfl

def code {n : Nat} (t : Syntax n) : Nat := (toLiteral t).code

@[simp] theorem code_var {n : Nat} (v : Nat ⊕ Fin n) :
    code (.var v) = Nat.pair 0 (variableCode v) + 1 := rfl

@[simp] theorem code_zero (n : Nat) :
    code (n := n) (.func .zero Fin.elim0) = Nat.pair 1 0 + 1 := rfl

@[simp] theorem code_succ {n : Nat} (t : Syntax n) :
    code ((FirstOrder.Language.Functions.apply₁ (L := language Nat) ArithmeticSymbol.succ) t) = Nat.pair 2 (code t) + 1 := rfl

@[simp] theorem code_add {n : Nat} (t u : Syntax n) :
    code ((FirstOrder.Language.Functions.apply₂ (L := language Nat) ArithmeticSymbol.add) t u) = Nat.pair 3 (Nat.pair (code t) (code u)) + 1 := rfl

@[simp] theorem code_mul {n : Nat} (t u : Syntax n) :
    code ((FirstOrder.Language.Functions.apply₂ (L := language Nat) ArithmeticSymbol.mul) t u) = Nat.pair 4 (Nat.pair (code t) (code u)) + 1 := rfl

theorem code_injective {n : Nat} : Function.Injective (code (n := n)) := by
  intro t u h
  have ht : toLiteral t = toLiteral u := Term.code_injective h
  have hd := congrArg (ofLiteral n) ht
  exact Option.some.inj (by simpa only [ofLiteral_toLiteral] using hd)

noncomputable def decode (n c : Nat) : Option (Syntax n) := do
  let t ← Encodable.decode (α := Term) c
  ofLiteral n t

@[simp] theorem decode_code {n : Nat} (t : Syntax n) :
    decode n (code t) = some t := by
  have ht : Encodable.decode (α := Term) (toLiteral t).code = some (toLiteral t) :=
    by simpa only [Term.encode_eq_code] using (Encodable.encodek (toLiteral t))
  simp only [decode, code, ht]
  exact ofLiteral_toLiteral t

def isCode (n : Nat) : Nat → Bool
  | 0 => false
  | k + 1 =>
    let tag := k.unpair.1
    let p := k.unpair.2
    cond (tag == 0) (variableIsCode n p)
      (cond (tag == 1) (p == 0)
        (cond (tag == 2) (isCode n p)
          (cond ((tag == 3) || (tag == 4))
            (isCode n p.unpair.1 && isCode n p.unpair.2) false)))
termination_by c => c
decreasing_by
  all_goals
    have hp := Nat.unpair_right_le k
    have hl := Nat.unpair_left_le k.unpair.2
    have hr := Nat.unpair_right_le k.unpair.2
    omega

private def recognitionStep (n : Nat) (h : List Bool) : Bool :=
  let k := h.length - 1
  let tag := k.unpair.1
  let p := k.unpair.2
  cond (h.length == 0) false
    (cond (tag == 0) (variableIsCode n p)
      (cond (tag == 1) (p == 0)
        (cond (tag == 2) (h[p]?.getD false)
          (cond ((tag == 3) || (tag == 4))
            (h[p.unpair.1]?.getD false && h[p.unpair.2]?.getD false) false))))

private theorem recognitionStep_primrec : Primrec₂ recognitionStep := by
  have hn : Primrec (fun p : Nat × List Bool => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hk := Primrec.nat_sub.comp hn (Primrec.const 1)
  have ht := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hp := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (j : Nat) := Primrec.beq.comp ht (Primrec.const j)
  have get (f : Nat × List Bool → Nat) (hf : Primrec f) :
      Primrec (fun p : Nat × List Bool => p.2[f p]?.getD false) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd hf)
      (Primrec.const false)
  exact ((Primrec.beq.comp hn (Primrec.const 0)).cond (Primrec.const false)
    ((test 0).cond (variableIsCode_primrec.comp Primrec.fst hp)
      ((test 1).cond (Primrec.beq.comp hp (Primrec.const 0))
        ((test 2).cond (get _ hp)
          ((Primrec.or.comp (test 3) (test 4)).cond
            (Primrec.and.comp (get _ hl) (get _ hr)) (Primrec.const false)))))).to₂

theorem isCode_primrec : Primrec₂ isCode := by
  have hg := Primrec.option_some.comp₂ recognitionStep_primrec
  exact Primrec.nat_strong_rec isCode hg (by
    intro n c
    cases c with
    | zero => simp [recognitionStep, isCode]
    | succ k =>
      have hp : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : k.unpair.2.unpair.1 < k + 1 :=
        lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : k.unpair.2.unpair.2 < k + 1 :=
        lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [recognitionStep, isCode, hp, hl, hr])

@[simp] theorem isCode_code {n : Nat} (t : Syntax n) : isCode n (code t) = true := by
  induction t with
  | var v => simp [code, toLiteral, Term.code, isCode, Nat.unpair_pair]
  | func f ts ih =>
    cases f <;> simp_all [code, toLiteral, Term.code, isCode, Nat.unpair_pair]

theorem isCode_sound (n c : Nat) : isCode n c = true → ∃ t : Syntax n, (code t) = c := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    cases c with
    | zero => simp [isCode]
    | succ k =>
      intro hc
      let tag := k.unpair.1
      let p := k.unpair.2
      have hp : p < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hl : p.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le p) hp
      have hr : p.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le p) hp
      have hk : k = Nat.pair tag p := (Nat.pair_unpair k).symm
      by_cases h0 : tag = 0
      · have hv : variableIsCode n p = true := by simpa [isCode, tag, p, h0] using hc
        obtain ⟨v, hv⟩ := variableIsCode_sound n p hv
        refine ⟨.var v, ?_⟩
        rw [hk, h0]
        simp only [code_var, hv]
      by_cases h1 : tag = 1
      · have hp0 : p = 0 := by simpa [isCode, tag, p, h0, h1] using hc
        refine ⟨.func .zero Fin.elim0, ?_⟩
        rw [hk, h1, hp0]
        rfl
      by_cases h2 : tag = 2
      · have ht : isCode n p = true := by simpa [isCode, tag, p, h0, h1, h2] using hc
        obtain ⟨t, ht⟩ := ih p hp ht
        refine ⟨(FirstOrder.Language.Functions.apply₁ (L := language Nat) ArithmeticSymbol.succ) t, ?_⟩
        rw [hk, h2]
        simp only [code_succ, ht]
      by_cases h3 : tag = 3
      · have ht : isCode n p.unpair.1 = true ∧ isCode n p.unpair.2 = true := by
          simpa [isCode, tag, p, h0, h1, h2, h3] using hc
        obtain ⟨t, ht1⟩ := ih _ hl ht.1
        obtain ⟨u, hu⟩ := ih _ hr ht.2
        refine ⟨(FirstOrder.Language.Functions.apply₂ (L := language Nat) ArithmeticSymbol.add) t u, ?_⟩
        rw [hk, h3]
        simp only [code_add, ht1, hu, Nat.pair_unpair]
      by_cases h4 : tag = 4
      · have ht : isCode n p.unpair.1 = true ∧ isCode n p.unpair.2 = true := by
          simpa [isCode, tag, p, h0, h1, h2, h3, h4] using hc
        obtain ⟨t, ht1⟩ := ih _ hl ht.1
        obtain ⟨u, hu⟩ := ih _ hr ht.2
        refine ⟨(FirstOrder.Language.Functions.apply₂ (L := language Nat) ArithmeticSymbol.mul) t u, ?_⟩
        rw [hk, h4]
        simp only [code_mul, ht1, hu, Nat.pair_unpair]
      simp [isCode, tag, p, h0, h1, h2, h3, h4] at hc

theorem isCode_iff (n c : Nat) : isCode n c = true ↔ ∃ t : Syntax n, (code t) = c :=
  ⟨isCode_sound n c, by rintro ⟨t, rfl⟩; exact isCode_code t⟩

noncomputable def codeEquiv (n : Nat) : Syntax n ≃ {c : Nat // isCode n c = true} where
  toFun := fun t => ⟨(code t), isCode_code t⟩
  invFun := fun c => Classical.choose (isCode_sound n c.val c.property)
  left_inv := fun t => code_injective
    (Classical.choose_spec (isCode_sound n (code t) (isCode_code t)))
  right_inv := fun c => Subtype.ext
    (Classical.choose_spec (isCode_sound n c.val c.property))

noncomputable instance syntaxPrimcodable (n : Nat) : Primcodable (Syntax n) := by
  letI : Primcodable {c : Nat // isCode n c = true} :=
    Primcodable.subtype
      (Primrec.eq.comp (isCode_primrec.comp (Primrec.const n) Primrec.id)
        (Primrec.const true))
  exact Primcodable.ofEquiv {c : Nat // isCode n c = true} (codeEquiv n)

noncomputable instance (priority := 1100) syntaxEncodable (n : Nat) : Encodable (Syntax n) :=
  (syntaxPrimcodable n).toEncodable

@[simp] theorem encode_eq_code {n : Nat} (t : Syntax n) : Encodable.encode t = (code t) := rfl

theorem code_primrec (n : Nat) : Primrec (code (n := n)) := by
  exact Primrec.encode

noncomputable def decodeExact (n : Nat) : Nat → Option (Syntax n) :=
  Encodable.decode₂ (Syntax n)

theorem decodeExact_primrec (n : Nat) : Primrec (decodeExact n) := Primrec.decode₂

theorem decodeExact_eq_some_iff {n c : Nat} (t : Syntax n) :
    decodeExact n c = some t ↔ (code t) = c := by
  simpa only [decodeExact, encode_eq_code] using
    (Encodable.decode₂_eq_some (n := c) (a := t))

@[simp] theorem decodeExact_code {n : Nat} (t : Syntax n) :
    decodeExact n (code t) = some t := (decodeExact_eq_some_iff t).mpr rfl

theorem succ_primrec (n : Nat) :
    Primrec ((FirstOrder.Language.Functions.apply₁ (L := language Nat) ArithmeticSymbol.succ) : Syntax n → Syntax n) := by
  apply Primrec.encode_iff.1
  simpa only [encode_eq_code, code_succ] using
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2) (code_primrec n))

theorem add_primrec (n : Nat) :
    Primrec₂ ((FirstOrder.Language.Functions.apply₂ (L := language Nat) ArithmeticSymbol.add) : Syntax n → Syntax n → Syntax n) := by
  apply Primrec.encode_iff.1
  have hp := Primrec₂.natPair.comp ((code_primrec n).comp Primrec.fst)
    ((code_primrec n).comp Primrec.snd)
  simpa only [encode_eq_code, code_add] using
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 3) hp)

theorem mul_primrec (n : Nat) :
    Primrec₂ ((FirstOrder.Language.Functions.apply₂ (L := language Nat) ArithmeticSymbol.mul) : Syntax n → Syntax n → Syntax n) := by
  apply Primrec.encode_iff.1
  have hp := Primrec₂.natPair.comp ((code_primrec n).comp Primrec.fst)
    ((code_primrec n).comp Primrec.snd)
  simpa only [encode_eq_code, code_mul] using
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 4) hp)

def freeVariableEquiv : Nat ≃ Nat ⊕ Fin 0 where
  toFun := Sum.inl
  invFun := Sum.elim id Fin.elim0
  left_inv := fun _ => rfl
  right_inv := by
    intro v
    cases v with
    | inl x => rfl
    | inr i => exact Fin.elim0 i

abbrev FreeSyntax := (language Nat).Term Nat

def freeTermEquiv : FreeSyntax ≃ Syntax 0 :=
  FirstOrder.Language.Term.relabelEquiv freeVariableEquiv

def freeCode (t : FreeSyntax) : Nat := code (freeTermEquiv t)

noncomputable instance freeSyntaxPrimcodable : Primcodable FreeSyntax :=
  Primcodable.ofEquiv (Syntax 0) freeTermEquiv

noncomputable instance (priority := 1100) freeSyntaxEncodable : Encodable FreeSyntax :=
  freeSyntaxPrimcodable.toEncodable

@[simp] theorem free_encode_eq_code (t : FreeSyntax) : Encodable.encode t = freeCode t := rfl

theorem freeCode_primrec : Primrec freeCode := by
  exact Primrec.encode

end Alexander313.Delta.NativeTerm
