import Alexander313.Alexander.NativeTupleFormation

/-!
# Exact primitive-recursive native Δ formula labels

Every node records its bound context. Relation nodes contain a literal owner
and source-formula label and an exact native argument tuple of the computed
arity. Quantifiers require their child's context to increase by one. The
finite-history recognizer thus checks actual native bounded formulas, rather
than a tree grammar with unchecked labels.
-/

namespace Alexander313.Delta.NativeFormula

abbrev Syntax (n : Nat) := (language Nat).BoundedFormula Nat n

def relationCode {m : Nat} (r : Relation Nat m) : Nat :=
  Nat.pair r.val.1 (r.val.2.code id)

def code : {n : Nat} → Syntax n → Nat
  | n, .falsum => Nat.pair n (Nat.pair 0 0 + 1) + 1
  | n, .equal t u => Nat.pair n (Nat.pair 1 (Nat.pair (NativeTerm.code t) (NativeTerm.code u)) + 1) + 1
  | n, @FirstOrder.Language.BoundedFormula.rel _ _ _ m r ts =>
    Nat.pair n (Nat.pair 2 (Nat.pair
      (relationCode r) (NativeTuple.code ts)) + 1) + 1
  | n, .imp φ ψ => Nat.pair n (Nat.pair 3 (Nat.pair (code φ) (code ψ)) + 1) + 1
  | n, .all φ => Nat.pair n (Nat.pair 4 (code φ) + 1) + 1

@[simp] theorem code_falsum (n : Nat) :
    code (n := n) .falsum = Nat.pair n (Nat.pair 0 0 + 1) + 1 := rfl

@[simp] theorem code_equal {n : Nat} (t u : NativeTerm.Syntax n) :
    code (.equal t u) = Nat.pair n (Nat.pair 1 (Nat.pair (NativeTerm.code t) (NativeTerm.code u)) + 1) + 1 := rfl

@[simp] theorem code_rel {n m : Nat} (r : Relation Nat m)
    (ts : Fin m → NativeTerm.Syntax n) :
    code (.rel r ts) = Nat.pair n (Nat.pair 2 (Nat.pair
      (relationCode r) (NativeTuple.code ts)) + 1) + 1 := rfl

@[simp] theorem code_imp {n : Nat} (φ ψ : Syntax n) :
    code (φ.imp ψ) = Nat.pair n (Nat.pair 3 (Nat.pair (code φ) (code ψ)) + 1) + 1 := rfl

@[simp] theorem code_all {n : Nat} (φ : Syntax (n + 1)) :
    code φ.all = Nat.pair n (Nat.pair 4 (code φ) + 1) + 1 := rfl

def context (c : Nat) : Nat := (c - 1).unpair.1

theorem context_primrec : Primrec context :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))

@[simp] theorem context_code {n : Nat} (φ : Syntax n) : context (code φ) = n := by
  cases φ <;> simp [context, code, Nat.unpair_pair]

theorem code_injective {n : Nat} : Function.Injective (code (n := n)) := by
  intro φ χ h
  induction φ with
  | falsum =>
    cases χ <;> simp_all [code_falsum, code_equal, code_rel, code_imp, code_all,
      Nat.pair_eq_pair]
  | equal t u =>
    cases χ with
    | equal t' u' =>
      have hs : (NativeTerm.code t) = (NativeTerm.code t') ∧ (NativeTerm.code u) = (NativeTerm.code u') := by
        simpa only [code_equal, Nat.pair_eq_pair, Nat.add_left_inj, true_and] using h
      exact congrArg₂ FirstOrder.Language.BoundedFormula.equal
        (NativeTerm.code_injective hs.1) (NativeTerm.code_injective hs.2)
    | falsum => simp [code_equal, code_falsum, Nat.pair_eq_pair] at h
    | rel => simp [code_equal, code_rel, Nat.pair_eq_pair] at h
    | imp => simp [code_equal, code_imp, Nat.pair_eq_pair] at h
    | all => simp [code_equal, code_all, Nat.pair_eq_pair] at h
  | @rel n m r ts =>
    cases χ with
    | @rel _ l s us =>
      have hs : relationCode r = relationCode s ∧
          NativeTuple.code ts = NativeTuple.code us := by
        simpa only [code_rel, Nat.pair_eq_pair, Nat.add_left_inj, true_and] using h
      have hr : (⟨m, r⟩ : Σ l, Relation Nat l) = ⟨l, s⟩ :=
        Encodable.encode_injective
          (by simpa only [relationSigma_encode, relationCode] using hs.1)
      have hm : m = l := congrArg Sigma.fst hr
      subst l
      have hrs : r = s := eq_of_heq (Sigma.ext_iff.mp hr).2
      subst s
      exact congrArg (FirstOrder.Language.BoundedFormula.rel r)
        (NativeTuple.code_injective hs.2)
    | falsum => simp [code_rel, code_falsum, Nat.pair_eq_pair] at h
    | equal => simp [code_rel, code_equal, Nat.pair_eq_pair] at h
    | imp => simp [code_rel, code_imp, Nat.pair_eq_pair] at h
    | all => simp [code_rel, code_all, Nat.pair_eq_pair] at h
  | imp φ ψ ihφ ihψ =>
    cases χ with
    | imp φ' ψ' =>
      have hs : code φ = code φ' ∧ code ψ = code ψ' := by
        simpa only [code_imp, Nat.pair_eq_pair, Nat.add_left_inj, true_and] using h
      exact congrArg₂ FirstOrder.Language.BoundedFormula.imp
        (by apply ihφ; exact hs.1) (by apply ihψ; exact hs.2)
    | falsum => simp [code_imp, code_falsum, Nat.pair_eq_pair] at h
    | equal => simp [code_imp, code_equal, Nat.pair_eq_pair] at h
    | rel => simp [code_imp, code_rel, Nat.pair_eq_pair] at h
    | all => simp [code_imp, code_all, Nat.pair_eq_pair] at h
  | all φ ih =>
    cases χ with
    | all ψ =>
      have hs : code φ = code ψ := by
        simpa only [code_all, Nat.pair_eq_pair, Nat.add_left_inj, true_and] using h
      exact congrArg FirstOrder.Language.BoundedFormula.all (by apply ih; exact hs)
    | falsum => simp [code_all, code_falsum, Nat.pair_eq_pair] at h
    | equal => simp [code_all, code_equal, Nat.pair_eq_pair] at h
    | rel => simp [code_all, code_rel, Nat.pair_eq_pair] at h
    | imp => simp [code_all, code_imp, Nat.pair_eq_pair] at h

theorem sigma_code_injective :
    Function.Injective (fun φ : Σ n, Syntax n => code φ.2) := by
  rintro ⟨n, φ⟩ ⟨m, ψ⟩ h
  have hn : n = m := by simpa only [context_code] using congrArg context h
  cases hn
  have hp : φ = ψ := code_injective h
  cases hp
  rfl

private def relationEntry (n p : Nat) : Bool :=
  Formula.isCode p.unpair.1.unpair.2 &&
    NativeTuple.isCode n (Formula.freeVariableCardCode p.unpair.1.unpair.2) p.unpair.2

private theorem relationEntry_primrec : Primrec₂ relationEntry := by
  have hp : Primrec (fun q : Nat × Nat => q.2.unpair) :=
    Primrec.unpair.comp Primrec.snd
  have hr := Primrec.fst.comp hp
  have hb := Primrec.snd.comp (Primrec.unpair.comp hr)
  have ht := Primrec.snd.comp hp
  exact (Primrec.and.comp (Formula.isCode_primrec.comp hb)
    (NativeTuple.isCode_primrec.comp
      ((Primrec.pair Primrec.fst (Formula.freeVariableCardCode_primrec.comp hb)).pair ht))).to₂

def isCode : Nat → Bool
  | 0 => false
  | k + 1 =>
    let n := k.unpair.1
    let b := k.unpair.2
    let tag := (b - 1).unpair.1
    let p := (b - 1).unpair.2
    cond (b == 0) false
      (cond (tag == 0) (p == 0)
        (cond (tag == 1) (NativeTerm.isCode n p.unpair.1 && NativeTerm.isCode n p.unpair.2)
          (cond (tag == 2) (relationEntry n p)
            (cond (tag == 3)
              ((context p.unpair.1 == n) && (context p.unpair.2 == n) &&
                (isCode p.unpair.1 && isCode p.unpair.2))
              (cond (tag == 4) ((context p == n + 1) && isCode p) false)))))
termination_by c => c
decreasing_by
  all_goals
    have hb := Nat.unpair_right_le k
    have hk := Nat.sub_le k.unpair.2 1
    have hp := Nat.unpair_right_le (k.unpair.2 - 1)
    have hl := Nat.unpair_left_le (k.unpair.2 - 1).unpair.2
    have hr := Nat.unpair_right_le (k.unpair.2 - 1).unpair.2
    omega

private def recognitionStep (h : List Bool) : Bool :=
  let k := h.length - 1
  let n := k.unpair.1
  let b := k.unpair.2
  let tag := (b - 1).unpair.1
  let p := (b - 1).unpair.2
  cond (h.length == 0) false
    (cond (b == 0) false
      (cond (tag == 0) (p == 0)
        (cond (tag == 1) (NativeTerm.isCode n p.unpair.1 && NativeTerm.isCode n p.unpair.2)
          (cond (tag == 2) (relationEntry n p)
            (cond (tag == 3)
              ((context p.unpair.1 == n) && (context p.unpair.2 == n) &&
                (h[p.unpair.1]?.getD false && h[p.unpair.2]?.getD false))
              (cond (tag == 4) ((context p == n + 1) && h[p]?.getD false) false))))))

private theorem recognitionStep_primrec : Primrec recognitionStep := by
  have hk : Primrec (fun h : List Bool => h.length - 1) :=
    Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)
  have hn := Primrec.fst.comp (Primrec.unpair.comp hk)
  have hb := Primrec.snd.comp (Primrec.unpair.comp hk)
  have hnode := Primrec.unpair.comp (Primrec.nat_sub.comp hb (Primrec.const 1))
  have ht := Primrec.fst.comp hnode
  have hp := Primrec.snd.comp hnode
  have hl := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hp)
  have test (t : Nat) := Primrec.beq.comp ht (Primrec.const t)
  have get (f : List Bool → Nat) (hf : Primrec f) :
      Primrec (fun h : List Bool => h[f h]?.getD false) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id hf)
      (Primrec.const false)
  exact (Primrec.beq.comp Primrec.list_length (Primrec.const 0)).cond
    (Primrec.const false)
    ((Primrec.beq.comp hb (Primrec.const 0)).cond (Primrec.const false)
      ((test 0).cond (Primrec.beq.comp hp (Primrec.const 0))
        ((test 1).cond
          (Primrec.and.comp (NativeTerm.isCode_primrec.comp hn hl)
            (NativeTerm.isCode_primrec.comp hn hr))
          ((test 2).cond (relationEntry_primrec.comp hn hp)
            ((test 3).cond
              (Primrec.and.comp
                (Primrec.and.comp (Primrec.beq.comp (context_primrec.comp hl) hn)
                  (Primrec.beq.comp (context_primrec.comp hr) hn))
                (Primrec.and.comp (get _ hl) (get _ hr)))
              ((test 4).cond
                (Primrec.and.comp (Primrec.beq.comp (context_primrec.comp hp)
                  (Primrec.succ.comp hn)) (get _ hp)) (Primrec.const false)))))))

theorem isCode_primrec : Primrec isCode := by
  have hg : Primrec₂ (fun (_ : Unit) (h : List Bool) => some (recognitionStep h)) :=
    ((Primrec.option_some.comp recognitionStep_primrec).comp Primrec.snd).to₂
  have htable := Primrec.nat_strong_rec (fun (_ : Unit) c => isCode c) hg (by
    intro a c
    cases c with
    | zero => simp [recognitionStep, isCode]
    | succ k =>
      have hb := Nat.unpair_right_le k
      have hk := Nat.sub_le k.unpair.2 1
      have hp₀ := Nat.unpair_right_le (k.unpair.2 - 1)
      have hp : (k.unpair.2 - 1).unpair.2 < k + 1 := by omega
      have hl : (k.unpair.2 - 1).unpair.2.unpair.1 < k + 1 :=
        lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have hr : (k.unpair.2 - 1).unpair.2.unpair.2 < k + 1 :=
        lt_of_le_of_lt (Nat.unpair_right_le _) hp
      simp [recognitionStep, isCode, hp, hl, hr])
  exact htable.comp (Primrec.const ()) Primrec.id

@[simp] theorem isCode_code {n : Nat} (φ : Syntax n) : isCode (code φ) = true := by
  induction φ with
  | falsum => simp [code, isCode, Nat.unpair_pair]
  | equal t u => simp [code, isCode, Nat.unpair_pair]
  | rel r ts =>
    simp [code, isCode, relationEntry, relationCode, Nat.unpair_pair,
      r.property]
  | imp φ ψ ihφ ihψ => simp [code, isCode, Nat.unpair_pair, ihφ, ihψ]
  | all φ ih => simp [code, isCode, Nat.unpair_pair, ih]

theorem isCode_sound (c : Nat) : isCode c = true → ∃ φ : Σ n, Syntax n, code φ.2 = c := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    cases c with
    | zero => simp [isCode]
    | succ k =>
      intro hc
      let n := k.unpair.1
      let b := k.unpair.2
      let tag := (b - 1).unpair.1
      let p := (b - 1).unpair.2
      have hb : b ≠ 0 := by
        intro hb
        simp [isCode, b, hb] at hc
      have hk : k = Nat.pair n b := (Nat.pair_unpair k).symm
      have hbody : b = Nat.pair tag p + 1 := by
        have hp := Nat.pair_unpair (b - 1)
        change Nat.pair tag p = b - 1 at hp
        omega
      have hp : p < k + 1 := by
        have h₁ := Nat.unpair_right_le (b - 1)
        have h₂ := Nat.sub_le b 1
        have h₃ := Nat.unpair_right_le k
        change p ≤ b - 1 at h₁
        change b ≤ k at h₃
        omega
      have hl : p.unpair.1 < k + 1 := lt_of_le_of_lt (Nat.unpair_left_le p) hp
      have hr : p.unpair.2 < k + 1 := lt_of_le_of_lt (Nat.unpair_right_le p) hp
      by_cases h0 : tag = 0
      · have hp0 : p = 0 := by simpa [isCode, n, b, tag, p, hb, h0] using hc
        refine ⟨⟨n, .falsum⟩, ?_⟩
        rw [hk, hbody, h0, hp0]
        rfl
      by_cases h1 : tag = 1
      · have ht : NativeTerm.isCode n p.unpair.1 = true ∧
            NativeTerm.isCode n p.unpair.2 = true := by
          simpa [isCode, n, b, tag, p, hb, h0, h1] using hc
        obtain ⟨t, ht1⟩ := NativeTerm.isCode_sound n _ ht.1
        obtain ⟨u, hu⟩ := NativeTerm.isCode_sound n _ ht.2
        refine ⟨⟨n, .equal t u⟩, ?_⟩
        rw [hk, hbody, h1]
        simp only [code_equal, ht1, hu, Nat.pair_unpair]
      by_cases h2 : tag = 2
      · have hs : Formula.isCode p.unpair.1.unpair.2 = true ∧
            NativeTuple.isCode n (Formula.freeVariableCardCode p.unpair.1.unpair.2)
              p.unpair.2 = true := by
          simpa [isCode, relationEntry, n, b, tag, p, hb, h0, h1, h2] using hc
        obtain ⟨φ, hφ⟩ := Formula.isCode_sound _ hs.1
        have ht : NativeTuple.isCode n φ.freeVars.card p.unpair.2 = true := by
          simpa only [← hφ, Formula.freeVariableCardCode_code] using hs.2
        obtain ⟨ts, hts⟩ := NativeTuple.isCode_sound n _ _ ht
        refine ⟨⟨n, .rel (modalSymbol p.unpair.1.unpair.1 φ) ts⟩, ?_⟩
        rw [hk, hbody, h2]
        simp only [code_rel, relationCode, modalSymbol, hφ, hts, Nat.pair_unpair]
      by_cases h3 : tag = 3
      · have hs : (context p.unpair.1 = n ∧ context p.unpair.2 = n) ∧
            (isCode p.unpair.1 = true ∧ isCode p.unpair.2 = true) := by
          simpa [isCode, n, b, tag, p, hb, h0, h1, h2, h3] using hc
        obtain ⟨⟨m, φ⟩, hφ⟩ := ih _ hl hs.2.1
        obtain ⟨⟨l, ψ⟩, hψ⟩ := ih _ hr hs.2.2
        have hm : m = n := by simpa only [← hφ, context_code] using hs.1.1
        have hn : l = n := by simpa only [← hψ, context_code] using hs.1.2
        subst m
        subst l
        refine ⟨⟨n, φ.imp ψ⟩, ?_⟩
        rw [hk, hbody, h3]
        simp only [code_imp, hφ, hψ, Nat.pair_unpair]
      by_cases h4 : tag = 4
      · have hs : context p = n + 1 ∧ isCode p = true := by
          simpa [isCode, n, b, tag, p, hb, h0, h1, h2, h3, h4] using hc
        obtain ⟨⟨m, φ⟩, hφ⟩ := ih _ hp hs.2
        have hm : m = n + 1 := by simpa only [← hφ, context_code] using hs.1
        subst m
        refine ⟨⟨n, φ.all⟩, ?_⟩
        rw [hk, hbody, h4]
        simp only [code_all, hφ]
      simp [isCode, n, b, tag, p, hb, h0, h1, h2, h3, h4] at hc

theorem isCode_iff (c : Nat) :
    isCode c = true ↔ ∃ φ : Σ n, Syntax n, code φ.2 = c :=
  ⟨isCode_sound c, by rintro ⟨φ, rfl⟩; exact isCode_code φ.2⟩

def isCodeAt (n c : Nat) : Bool := (context c == n) && isCode c

theorem isCodeAt_primrec : Primrec₂ isCodeAt :=
  (Primrec.and.comp (Primrec.beq.comp (context_primrec.comp Primrec.snd) Primrec.fst)
    (isCode_primrec.comp Primrec.snd)).to₂

@[simp] theorem isCodeAt_code {n : Nat} (φ : Syntax n) : isCodeAt n (code φ) = true := by
  simp [isCodeAt]

theorem isCodeAt_sound (n c : Nat) (h : isCodeAt n c = true) :
    ∃ φ : Syntax n, code φ = c := by
  have hs : context c = n ∧ isCode c = true := by simpa [isCodeAt] using h
  obtain ⟨⟨m, φ⟩, hφ⟩ := isCode_sound c hs.2
  have hm : m = n := by simpa only [← hφ, context_code] using hs.1
  subst m
  exact ⟨φ, hφ⟩

theorem isCodeAt_iff (n c : Nat) :
    isCodeAt n c = true ↔ ∃ φ : Syntax n, code φ = c :=
  ⟨isCodeAt_sound n c, by rintro ⟨φ, rfl⟩; exact isCodeAt_code φ⟩

noncomputable def sigmaCodeEquiv : (Σ n, Syntax n) ≃ {c : Nat // isCode c = true} where
  toFun := fun φ => ⟨code φ.2, isCode_code φ.2⟩
  invFun := fun c => Classical.choose (isCode_sound c.val c.property)
  left_inv := fun φ => sigma_code_injective
    (Classical.choose_spec (isCode_sound (code φ.2) (isCode_code φ.2)))
  right_inv := fun c => Subtype.ext (Classical.choose_spec (isCode_sound c.val c.property))

noncomputable instance sigmaPrimcodable : Primcodable (Σ n, Syntax n) := by
  letI : Primcodable {c : Nat // isCode c = true} :=
    Primcodable.subtype (Primrec.eq.comp isCode_primrec (Primrec.const true))
  exact Primcodable.ofEquiv {c : Nat // isCode c = true} sigmaCodeEquiv

noncomputable def codeEquiv (n : Nat) : Syntax n ≃ {c : Nat // isCodeAt n c = true} where
  toFun := fun φ => ⟨code φ, isCodeAt_code φ⟩
  invFun := fun c => Classical.choose (isCodeAt_sound n c.val c.property)
  left_inv := fun φ => code_injective
    (Classical.choose_spec (isCodeAt_sound n (code φ) (isCodeAt_code φ)))
  right_inv := fun c => Subtype.ext
    (Classical.choose_spec (isCodeAt_sound n c.val c.property))

noncomputable instance syntaxPrimcodable (n : Nat) : Primcodable (Syntax n) := by
  letI : Primcodable {c : Nat // isCodeAt n c = true} :=
    Primcodable.subtype
      (Primrec.eq.comp (isCodeAt_primrec.comp (Primrec.const n) Primrec.id)
        (Primrec.const true))
  exact Primcodable.ofEquiv {c : Nat // isCodeAt n c = true} (codeEquiv n)

noncomputable instance (priority := 1100) sigmaEncodable : Encodable (Σ n, Syntax n) :=
  sigmaPrimcodable.toEncodable

@[simp] theorem sigma_encode_eq_code (φ : Σ n, Syntax n) :
    Encodable.encode φ = code φ.2 := rfl

@[simp] theorem encode_eq_code {n : Nat} (φ : Syntax n) : Encodable.encode φ = code φ := rfl

theorem code_primrec (n : Nat) : Primrec (code (n := n)) := by
  exact Primrec.encode

noncomputable def decodeExact (n : Nat) : Nat → Option (Syntax n) :=
  Encodable.decode₂ (Syntax n)

theorem decodeExact_primrec (n : Nat) : Primrec (decodeExact n) := Primrec.decode₂

theorem decodeExact_eq_some_iff {n c : Nat} (φ : Syntax n) :
    decodeExact n c = some φ ↔ code φ = c := by
  simpa only [decodeExact, encode_eq_code] using
    (Encodable.decode₂_eq_some (n := c) (a := φ))

@[simp] theorem decodeExact_code {n : Nat} (φ : Syntax n) :
    decodeExact n (code φ) = some φ := (decodeExact_eq_some_iff φ).mpr rfl

theorem equal_primrec (n : Nat) : Primrec₂
    (FirstOrder.Language.BoundedFormula.equal :
      NativeTerm.Syntax n → NativeTerm.Syntax n → Syntax n) := by
  apply Primrec.encode_iff.1
  have hp := Primrec₂.natPair.comp ((NativeTerm.code_primrec n).comp Primrec.fst)
    ((NativeTerm.code_primrec n).comp Primrec.snd)
  have hb := Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) hp)
  simpa only [encode_eq_code, code_equal] using
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const n) hb)

theorem imp_primrec (n : Nat) : Primrec₂
    (FirstOrder.Language.BoundedFormula.imp : Syntax n → Syntax n → Syntax n) := by
  apply Primrec.encode_iff.1
  have hp := Primrec₂.natPair.comp ((code_primrec n).comp Primrec.fst)
    ((code_primrec n).comp Primrec.snd)
  have hb := Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 3) hp)
  simpa only [encode_eq_code, code_imp] using
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const n) hb)

theorem all_primrec (n : Nat) : Primrec
    (FirstOrder.Language.BoundedFormula.all : Syntax (n + 1) → Syntax n) := by
  apply Primrec.encode_iff.1
  have hb := Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 4) (code_primrec (n + 1)))
  simpa only [encode_eq_code, code_all] using
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const n) hb)

end Alexander313.Delta.NativeFormula
