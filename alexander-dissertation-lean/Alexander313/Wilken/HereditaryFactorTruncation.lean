import Alexander313.Wilken.HereditaryMultiplicativeNormalForm
import Alexander313.Wilken.MultiplicativeFactorTruncation

/-!
# Executing overlined multiplicative factor truncation

The genuine principal logarithm supplies the exponent of an original positive
additive principal. An actual PR comparison retains precisely those canonical
MNF factors whose values are at least the original threshold. The retained
exponent heads are summed by actual canonical addition, and omega power of
that sum computes their ordered product. Empty retention gives canonical one.
The logarithm search is partial recursive; no PR claim is made for truncation.
Exact domains, canonical output, literal retained words and graph certificates
are proved from this algorithm. This does not implement the sk iteration,
which additionally needs genuine mu and native height. Terms are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.FactorTruncation

open Alexander313.Wilken.MultiplicativeNormalForm (factorProduct omegaFactors)

/-- Compare the actual factor, not its exponent, with the original threshold. -/
def keep (b a : Nat) : Bool :=
  !Alexander313.HereditaryOrdinalFormation.unionLess (OmegaPowers.powerCode a) b

theorem keep_primrec : Primrec₂ keep :=
  (Primrec.not.comp (Alexander313.HereditaryOrdinalFormation.unionLess_primrec.comp
    (OmegaPowers.powerCode_primrec.comp Primrec.snd) Primrec.fst)).to₂

theorem keep_exact (b a : Nat) (hb : unionCheck b = true) (ha : unionCheck a = true) :
    keep b a = true ↔ unionInterpretation b ≤ Ordinal.omega0 ^ unionInterpretation a := by
  constructor
  · intro hk
    apply le_of_not_gt
    intro hlt
    have hl : Alexander313.HereditaryOrdinalFormation.unionLess (OmegaPowers.powerCode a) b = true :=
      (Alexander313.HereditaryOrdinalFormation.unionLess_exact _ _).mpr
        ⟨OmegaPowers.powerCode_original a ha, hb, by rw [OmegaPowers.powerCode_value a ha]; exact hlt⟩
    simp only [keep, hl, Bool.not_true, Bool.false_eq_true] at hk
  · intro hle
    have hn : ¬Alexander313.HereditaryOrdinalFormation.unionLess (OmegaPowers.powerCode a) b = true := by
      intro hl
      have hlt := ((Alexander313.HereditaryOrdinalFormation.unionLess_exact _ _).mp hl).2.2
      rw [OmegaPowers.powerCode_value a ha] at hlt
      exact not_lt_of_ge hle hlt
    have hf := Bool.eq_false_of_not_eq_true hn
    simp only [keep, hf, Bool.not_false]

/-- A real finite fold; no supplied filter or decision oracle. -/
def select (b : Nat) : List Nat → List Nat
  | [] => []
  | a :: xs => cond (keep b a) (a :: select b xs) (select b xs)

theorem select_primrec : Primrec₂ select := by
  have hs : Primrec₂ (fun (p : Nat × List Nat) (s : Nat × List Nat) =>
      cond (keep p.1 s.1) (s.1 :: s.2) s.2) :=
    (Primrec.cond (keep_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const []) hs
  have he : (fun p : Nat × List Nat => p.2.foldr
      (fun a xs => cond (keep p.1 a) (a :: xs) xs) []) = fun p => select p.1 p.2 := by
    funext p
    rcases p with ⟨b, xs⟩
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.foldr_cons, select, ih]
  have hresult := h.of_eq (fun p => congrFun he p)
  exact hresult.to₂

theorem select_mem (b : Nat) (xs : List Nat) (a : Nat) :
    a ∈ select b xs ↔ a ∈ xs ∧ keep b a = true := by
  induction xs with
  | nil => simp only [select, List.not_mem_nil, false_and]
  | cons c cs ih =>
    cases hk : keep b c with
    | false =>
      simp only [select, hk, Bool.cond_false, ih, List.mem_cons]
      constructor
      · intro h; exact ⟨Or.inr h.1, h.2⟩
      · rintro ⟨h | h, ha⟩
        · subst a; simp only [hk, Bool.false_eq_true] at ha
        · exact ⟨h, ha⟩
    | true =>
      simp only [select, hk, Bool.cond_true, List.mem_cons, ih]
      constructor
      · rintro (h | h)
        · subst a; exact ⟨Or.inl rfl, hk⟩
        · exact ⟨Or.inr h.1, h.2⟩
      · rintro ⟨h | h, ha⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, ha⟩

theorem select_values (b : Nat) (xs : List Nat) (hb : unionCheck b = true)
    (hx : ∀ a ∈ xs, unionCheck a = true) :
    (select b xs).map (fun a => Ordinal.omega0 ^ unionInterpretation a) =
      Alexander313.Wilken.MultiplicativeFactorTruncation.retain (unionInterpretation b)
        (xs.map (fun a => Ordinal.omega0 ^ unionInterpretation a)) := by
  classical
  revert hx
  induction xs with
  | nil => intro _; rfl
  | cons a xs ih =>
    intro hx
    have hv : keep b a = decide (unionInterpretation b ≤ Ordinal.omega0 ^ unionInterpretation a) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using keep_exact b a hb (hx a List.mem_cons_self)
    have ht := ih (fun c hc => hx c (List.mem_cons_of_mem _ hc))
    cases hk : keep b a <;>
      simp [select, hk, Alexander313.Wilken.MultiplicativeFactorTruncation.retain,
        ← hv, ht]

def retainedExponents (b d : Nat) : List Nat := select b (CanonicalCoefficients.word d)

theorem retainedExponents_primrec : Primrec₂ retainedExponents :=
  (select_primrec.comp Primrec.fst (CanonicalCoefficients.word_primrec.comp Primrec.snd)).to₂

theorem retainedExponents_head (b d a : Nat) (hd : unionCheck d = true)
    (ha : a ∈ retainedExponents b d) : Canonical.check a = true :=
  (CanonicalCoefficients.word_head_spec d hd a ((select_mem b _ a).mp ha).1).1

def retainedWord (b d : Nat) : List Nat := (retainedExponents b d).map OmegaPowers.powerCode

theorem retainedWord_primrec : Primrec₂ retainedWord :=
  (Primrec.list_map retainedExponents_primrec
    (OmegaPowers.powerCode_primrec.comp Primrec.snd).to₂).to₂

theorem retainedWord_head (b d c : Nat) (hd : unionCheck d = true) (hc : c ∈ retainedWord b d) :
    Canonical.check c = true ∧ 1 < unionInterpretation c ∧
      Alexander313.Wilken.MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation c) := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
  apply MultiplicativeNormalForm.factorWord_head_spec d hd
  exact List.mem_map.mpr ⟨a, ((select_mem b _ a).mp ha).1, rfl⟩

theorem retainedWord_power_values (b d : Nat) (hd : unionCheck d = true) :
    (retainedWord b d).map unionInterpretation =
      (retainedExponents b d).map (fun a => Ordinal.omega0 ^ unionInterpretation a) := by
  simp only [retainedWord, List.map_map]
  apply List.map_congr_left
  intro a ha
  exact OmegaPowers.powerCode_value a (Canonical.check_original (retainedExponents_head b d a hd ha))

theorem retainedWord_values (b d : Nat) (hb : unionCheck b = true) (hd : unionCheck d = true) :
    (retainedWord b d).map unionInterpretation =
      Alexander313.Wilken.MultiplicativeFactorTruncation.retain (unionInterpretation b)
        (omegaFactors (unionInterpretation d)) := by
  rw [retainedWord_power_values b d hd, retainedExponents,
    select_values b _ hb (fun a ha => Canonical.check_original (CanonicalCoefficients.word_head_spec d hd a ha).1)]
  have hm : (CanonicalCoefficients.word d).map (fun a => Ordinal.omega0 ^ unionInterpretation a) =
      ((CanonicalCoefficients.word d).map unionInterpretation).map (fun a => Ordinal.omega0 ^ a) := by
    rw [List.map_map]
    rfl
  rw [hm, CanonicalCoefficients.word_anf d hd]
  rfl

/-- Ordered source sums of retained exponents. -/
def sumCodes : List Nat → Nat
  | [] => CanonicalArithmetic.numeralCode 0
  | a :: xs => CanonicalArithmetic.canonicalSum a (sumCodes xs)

theorem sumCodes_primrec : Primrec sumCodes := by
  have hs : Primrec₂ (fun (_ : List Nat) (s : Nat × Nat) => CanonicalArithmetic.canonicalSum s.1 s.2) :=
    (CanonicalArithmetic.canonicalSum_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.id (Primrec.const (CanonicalArithmetic.numeralCode 0)) hs
  have he : (fun xs : List Nat => xs.foldr CanonicalArithmetic.canonicalSum
      (CanonicalArithmetic.numeralCode 0)) = sumCodes := by
    funext xs
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.foldr_cons, sumCodes, ih]
  have hresult := h.of_eq (fun p => congrFun he p)
  exact hresult

theorem sumCodes_spec (xs : List Nat) (hx : ∀ a ∈ xs, unionCheck a = true) :
    Canonical.check (sumCodes xs) = true ∧
      unionInterpretation (sumCodes xs) = principalSum (xs.map unionInterpretation) := by
  revert hx
  induction xs with
  | nil =>
    intro _
    exact ⟨CanonicalArithmetic.numeralCode_checked 0, CanonicalArithmetic.numeralCode_value 0⟩
  | cons a xs ih =>
    intro hx
    have ht := ih (fun c hc => hx c (List.mem_cons_of_mem _ hc))
    have ha := hx a List.mem_cons_self
    exact ⟨CanonicalArithmetic.canonicalSum_checked a _ ha (Canonical.check_original ht.1),
      (CanonicalArithmetic.canonicalSum_value a _ ha (Canonical.check_original ht.1)).trans
        (by rw [ht.2]; rfl)⟩

def productCode (b d : Nat) : Nat := OmegaPowers.powerCode (sumCodes (retainedExponents b d))

theorem productCode_primrec : Primrec₂ productCode :=
  (OmegaPowers.powerCode_primrec.comp (sumCodes_primrec.comp retainedExponents_primrec)).to₂

theorem productCode_spec (b d : Nat) (hd : unionCheck d = true) :
    Canonical.check (productCode b d) = true ∧
      unionInterpretation (productCode b d) = factorProduct ((retainedWord b d).map unionInterpretation) := by
  have hs := sumCodes_spec (retainedExponents b d)
    (fun a ha => Canonical.check_original (retainedExponents_head b d a hd ha))
  refine ⟨OmegaPowers.powerCode_checked _ (Canonical.check_original hs.1), ?_⟩
  rw [productCode, OmegaPowers.powerCode_value _ (Canonical.check_original hs.1), hs.2,
    retainedWord_power_values b d hd]
  have hm : (retainedExponents b d).map (fun a => Ordinal.omega0 ^ unionInterpretation a) =
      ((retainedExponents b d).map unionInterpretation).map (fun a => Ordinal.omega0 ^ a) := by
    rw [List.map_map]
    rfl
  rw [hm, Alexander313.Wilken.MultiplicativeNormalForm.factorProduct_omega_map]

/-- The complete literal retained canonical word. -/
def encodeRetained (b d : Nat) : Nat := Encodable.encode (retainedWord b d)

theorem encodeRetained_primrec : Primrec₂ encodeRetained :=
  (Primrec.encode.comp retainedWord_primrec).to₂

def truncate (q b : Nat) : Part Nat := cond (unionCheck b)
  ((PrincipalLogarithm.logarithm q).map (productCode b)) Part.none

def retainedForm (q b : Nat) : Part Nat := cond (unionCheck b)
  ((PrincipalLogarithm.logarithm q).map (encodeRetained b)) Part.none

theorem truncate_partrec : Partrec₂ truncate :=
  (Partrec.cond (Uniform.unionCheck_primrec.comp Primrec.snd).to_comp
    (Partrec.map (PrincipalLogarithm.logarithm_partrec.comp Primrec.fst.to_comp)
      (productCode_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to_comp.to₂)
    Partrec.none).to₂

theorem retainedForm_partrec : Partrec₂ retainedForm :=
  (Partrec.cond (Uniform.unionCheck_primrec.comp Primrec.snd).to_comp
    (Partrec.map (PrincipalLogarithm.logarithm_partrec.comp Primrec.fst.to_comp)
      (encodeRetained_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to_comp.to₂)
    Partrec.none).to₂

theorem truncate_domain (q b : Nat) : (truncate q b).Dom ↔
    Principal.unionPrincipalCheck q = true ∧ unionCheck b = true := by
  cases hb : unionCheck b with
  | false => simp [truncate, hb]
  | true =>
    rw [truncate, hb, Bool.cond_true]
    change (PrincipalLogarithm.logarithm q).Dom ↔ _
    simpa only [hb, and_true] using PrincipalLogarithm.logarithm_domain q

theorem retainedForm_domain (q b : Nat) : (retainedForm q b).Dom ↔
    Principal.unionPrincipalCheck q = true ∧ unionCheck b = true := by
  cases hb : unionCheck b with
  | false => simp [retainedForm, hb]
  | true =>
    rw [retainedForm, hb, Bool.cond_true]
    change (PrincipalLogarithm.logarithm q).Dom ↔ _
    simpa only [hb, and_true] using PrincipalLogarithm.logarithm_domain q

def TruncateSpec (q b c : Nat) : Prop :=
  Principal.unionPrincipalCheck q = true ∧ unionCheck b = true ∧ Canonical.check c = true ∧
    unionInterpretation c = Alexander313.Wilken.MultiplicativeFactorTruncation.truncate
      (unionInterpretation q) (unionInterpretation b)

def RetainedSpec (q b : Nat) (rs : List Nat) : Prop :=
  Principal.unionPrincipalCheck q = true ∧ unionCheck b = true ∧
    (∀ c ∈ rs, Canonical.check c = true) ∧ rs.map unionInterpretation =
      Alexander313.Wilken.MultiplicativeFactorTruncation.retain (unionInterpretation b)
        (Alexander313.Wilken.MultiplicativeNormalForm.canonicalMNF (unionInterpretation q))

theorem retainedWord_spec (q b d : Nat) (hb : unionCheck b = true)
    (hd : PrincipalLogarithm.graph q d = true) : RetainedSpec q b (retainedWord b d) := by
  have hs := (PrincipalLogarithm.graph_exact q d).mp hd
  have hu := Canonical.check_original hs.2.2.2.1
  refine ⟨(Principal.unionPrincipalCheck_exact q).mpr ⟨hs.1, hs.2.1, hs.2.2.1⟩,
    hb, fun c hc => (retainedWord_head b d c hu hc).1, ?_⟩
  rw [retainedWord_values b d hb hu, ← hs.2.2.2.2,
    Alexander313.Wilken.MultiplicativeNormalForm.canonicalMNF_omegaPower]

theorem productCode_source (q b d : Nat) (hb : unionCheck b = true)
    (hd : PrincipalLogarithm.graph q d = true) : TruncateSpec q b (productCode b d) := by
  have hr := retainedWord_spec q b d hb hd
  have hp := productCode_spec b d
    (Canonical.check_original ((PrincipalLogarithm.graph_exact q d).mp hd).2.2.2.1)
  exact ⟨hr.1, hr.2.1, hp.1, hp.2.trans (by rw [hr.2.2.2]; rfl)⟩

theorem truncate_value (q b c : Nat) (hc : c ∈ truncate q b) : TruncateSpec q b c := by
  have hb := ((truncate_domain q b).mp (Part.dom_iff_mem.mpr ⟨_, hc⟩)).2
  rw [truncate, hb, Bool.cond_true] at hc
  obtain ⟨d, hd, he⟩ := (Part.mem_map_iff (productCode b)).mp hc
  rw [← he]
  exact productCode_source q b d hb (PrincipalLogarithm.logarithm_graph q d hd)

theorem retainedForm_spec (q b : Nat) (rs : List Nat) (hc : Encodable.encode rs ∈ retainedForm q b) :
    RetainedSpec q b rs := by
  have hb := ((retainedForm_domain q b).mp (Part.dom_iff_mem.mpr ⟨_, hc⟩)).2
  rw [retainedForm, hb, Bool.cond_true] at hc
  obtain ⟨d, hd, he⟩ := (Part.mem_map_iff (encodeRetained b)).mp hc
  have hrs : retainedWord b d = rs := Encodable.encode_injective he
  rw [← hrs]
  exact retainedWord_spec q b d hb (PrincipalLogarithm.logarithm_graph q d hd)

theorem truncate_returns (q b : Nat) (hq : Principal.unionPrincipalCheck q = true) (hb : unionCheck b = true) :
    ∃ c, c ∈ truncate q b ∧ TruncateSpec q b c := by
  have hd := (truncate_domain q b).mpr ⟨hq, hb⟩
  have hm := Part.get_mem hd
  exact ⟨_, hm, truncate_value q b _ hm⟩

theorem retainedForm_returns (q b : Nat) (hq : Principal.unionPrincipalCheck q = true) (hb : unionCheck b = true) :
    ∃ rs : List Nat, Encodable.encode rs ∈ retainedForm q b ∧ RetainedSpec q b rs := by
  obtain ⟨d, hd, _, _⟩ := PrincipalLogarithm.logarithm_returns q hq
  have hm : encodeRetained b d ∈ retainedForm q b := by
    rw [retainedForm, hb, Bool.cond_true]
    exact Part.mem_map (encodeRetained b) hd
  exact ⟨retainedWord b d, hm, retainedForm_spec q b _ hm⟩

theorem truncate_spec_unique (q v b t c d : Nat) (hc : TruncateSpec q b c) (hd : TruncateSpec v t d)
    (hqv : unionInterpretation q = unionInterpretation v) (hbt : unionInterpretation b = unionInterpretation t) : c = d :=
  Canonical.check_value_injective c d hc.2.2.1 hd.2.2.1
    (hc.2.2.2.trans (by rw [hqv, hbt]; exact hd.2.2.2.symm))

theorem retained_spec_unique (q v b t : Nat) (xs ys : List Nat) (hx : RetainedSpec q b xs)
    (hy : RetainedSpec v t ys) (hqv : unionInterpretation q = unionInterpretation v)
    (hbt : unionInterpretation b = unionInterpretation t) : xs = ys := by
  apply CanonicalCoefficients.checked_word_ext xs ys hx.2.2.1 hy.2.2.1
  rw [hx.2.2.2, hy.2.2.2, hqv, hbt]

theorem truncate_graph_iff (q b c : Nat) : c ∈ truncate q b ↔ TruncateSpec q b c := by
  constructor
  · exact truncate_value q b c
  · intro hs
    obtain ⟨d, hd, hds⟩ := truncate_returns q b hs.1 hs.2.1
    rw [truncate_spec_unique q q b b c d hs hds rfl rfl]
    exact hd

theorem retainedForm_graph_iff (q b c : Nat) : c ∈ retainedForm q b ↔
    ∃ rs : List Nat, c = Encodable.encode rs ∧ RetainedSpec q b rs := by
  constructor
  · intro hc
    have hb := ((retainedForm_domain q b).mp (Part.dom_iff_mem.mpr ⟨_, hc⟩)).2
    rw [retainedForm, hb, Bool.cond_true] at hc
    obtain ⟨d, hd, he⟩ := (Part.mem_map_iff (encodeRetained b)).mp hc
    exact ⟨retainedWord b d, he.symm,
      retainedWord_spec q b d hb (PrincipalLogarithm.logarithm_graph q d hd)⟩
  · rintro ⟨rs, rfl, hs⟩
    obtain ⟨ss, hc, hss⟩ := retainedForm_returns q b hs.1 hs.2.1
    rw [retained_spec_unique q q b b rs ss hs hss rfl rfl]
    exact hc

theorem truncate_unique (q b : Nat) (hq : Principal.unionPrincipalCheck q = true) (hb : unionCheck b = true) :
    ∃! c, c ∈ truncate q b := by
  obtain ⟨c, hc, hs⟩ := truncate_returns q b hq hb
  exact ⟨c, hc, fun d hd => truncate_spec_unique q q b b d c (truncate_value q b d hd) hs rfl rfl⟩

theorem retainedForm_unique (q b : Nat) (hq : Principal.unionPrincipalCheck q = true) (hb : unionCheck b = true) :
    ∃! c, c ∈ retainedForm q b := by
  obtain ⟨rs, hc, hs⟩ := retainedForm_returns q b hq hb
  refine ⟨Encodable.encode rs, hc, ?_⟩
  intro c hc
  obtain ⟨ss, he, hss⟩ := (retainedForm_graph_iff q b c).mp hc
  exact he.trans (congrArg Encodable.encode (retained_spec_unique q q b b ss rs hss hs rfl rfl))

theorem truncate_invariant (q v b t c d : Nat) (hc : c ∈ truncate q b) (hd : d ∈ truncate v t)
    (hqv : unionInterpretation q = unionInterpretation v) (hbt : unionInterpretation b = unionInterpretation t) : c = d :=
  truncate_spec_unique q v b t c d (truncate_value q b c hc) (truncate_value v t d hd) hqv hbt

theorem retainedForm_invariant (q v b t c d : Nat) (hc : c ∈ retainedForm q b) (hd : d ∈ retainedForm v t)
    (hqv : unionInterpretation q = unionInterpretation v) (hbt : unionInterpretation b = unionInterpretation t) : c = d := by
  obtain ⟨xs, hcx, hx⟩ := (retainedForm_graph_iff q b c).mp hc
  obtain ⟨ys, hdy, hy⟩ := (retainedForm_graph_iff v t d).mp hd
  exact hcx.trans ((congrArg Encodable.encode (retained_spec_unique q v b t xs ys hx hy hqv hbt)).trans hdy.symm)

theorem truncate_original (q b c : Nat) (hc : c ∈ truncate q b) :
    unionCheck c = true ∧ Theta.Normal c.unpair.1 (ThetaCourse.rawTree c.unpair.2) := by
  have hs := truncate_value q b c hc
  exact ⟨Canonical.check_original hs.2.2.1, Canonical.check_normal hs.2.2.1⟩

theorem truncate_principal (q b c : Nat) (hc : c ∈ truncate q b) :
    Principal.unionPrincipalCheck c = true := by
  have hs := truncate_value q b c hc
  have hp := Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_pos_principal
    (unionInterpretation q) (unionInterpretation b)
  apply (Principal.unionPrincipalCheck_exact c).mpr
  rw [hs.2.2.2]
  exact ⟨Canonical.check_original hs.2.2.1, hp⟩

theorem truncate_bounds (q b c : Nat) (hc : c ∈ truncate q b) :
    1 ≤ unionInterpretation c ∧ unionInterpretation c ≤ unionInterpretation q := by
  have hs := truncate_value q b c hc
  have hq := (Principal.unionPrincipalCheck_exact q).mp hs.1
  rw [hs.2.2.2]
  exact ⟨Order.one_le_iff_pos.mpr
    (Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_pos_principal _ _).1,
    Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_le hq.2.1 hq.2.2 _⟩

theorem truncate_idempotent (q b c : Nat) (hc : c ∈ truncate q b) : truncate c b = Part.some c := by
  have hs := truncate_value q b c hc
  apply Part.eq_some_iff.mpr
  apply (truncate_graph_iff c b c).mpr
  refine ⟨truncate_principal q b c hc, hs.2.1, hs.2.2.1, ?_⟩
  rw [hs.2.2.2, Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_idempotent]

theorem retainedForm_reduced (q b : Nat) (rs : List Nat) (hr : Encodable.encode rs ∈ retainedForm q b) :
    Alexander313.Wilken.MultiplicativeNormalForm.IsReducedMNF (rs.map unionInterpretation) := by
  rw [(retainedForm_spec q b rs hr).2.2.2]
  exact Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_reduced _ _

theorem retainedForm_head (q b : Nat) (rs : List Nat) (hr : Encodable.encode rs ∈ retainedForm q b)
    (c : Nat) (hc : c ∈ rs) : Canonical.check c = true ∧ 1 < unionInterpretation c ∧
      Alexander313.Wilken.MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation c) ∧
      unionInterpretation b ≤ unionInterpretation c := by
  have hs := retainedForm_spec q b rs hr
  have hm : unionInterpretation c ∈ rs.map unionInterpretation := List.mem_map.mpr ⟨c, hc, rfl⟩
  have hp := retainedForm_reduced q b rs hr
  refine ⟨hs.2.2.1 c hc, hp.2 _ hm, hp.1.1 _ hm, ?_⟩
  rw [hs.2.2.2] at hm
  exact ((Alexander313.Wilken.MultiplicativeFactorTruncation.retain_mem _ _ _).mp hm).2

theorem retainedForm_product (q b c : Nat) (rs : List Nat)
    (hr : Encodable.encode rs ∈ retainedForm q b) (hc : c ∈ truncate q b) :
    factorProduct (rs.map unionInterpretation) = unionInterpretation c := by
  rw [(retainedForm_spec q b rs hr).2.2.2, (truncate_value q b c hc).2.2.2]
  rfl

private theorem take_mem (xs : List Nat) (n a : Nat) (ha : a ∈ xs.take n) : a ∈ xs := by
  induction n generalizing xs with
  | zero => simp only [List.take_zero, List.not_mem_nil] at ha
  | succ n ih =>
    cases xs with
    | nil => simp only [List.take_nil, List.not_mem_nil] at ha
    | cons c cs =>
      change a ∈ c :: cs.take n at ha
      rcases List.mem_cons.mp ha with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr (ih cs h))

/-- Literal initial segment of the unique original canonical factor word. -/
theorem retainedForm_prefix (q b : Nat) (xs rs : List Nat)
    (hx : Encodable.encode xs ∈ MultiplicativeNormalForm.normalForm q)
    (hr : Encodable.encode rs ∈ retainedForm q b) : rs = xs.take rs.length := by
  have hs := retainedForm_spec q b rs hr
  have hxspec := MultiplicativeNormalForm.normalForm_spec q xs hx
  apply CanonicalCoefficients.checked_word_ext rs (xs.take rs.length) hs.2.2.1
    (fun c hc => hxspec.2.1 c (take_mem xs rs.length c hc))
  rw [List.map_take, MultiplicativeNormalForm.normalForm_values q xs hx, hs.2.2.2]
  have hl : rs.length =
      (Alexander313.Wilken.MultiplicativeFactorTruncation.retain (unionInterpretation b)
        (Alexander313.Wilken.MultiplicativeNormalForm.canonicalMNF (unionInterpretation q))).length := by
    rw [← hs.2.2.2, List.length_map]
  rw [hl]
  exact Alexander313.Wilken.MultiplicativeFactorTruncation.retain_eq_take _ _
    (Alexander313.Wilken.MultiplicativeNormalForm.canonicalMNF_reduced _).1.2

/-- The source lower bound requires the actual multiplicative threshold class. -/
theorem truncate_source_bounds (q b c : Nat) (hc : c ∈ truncate q b)
    (hm : Alexander313.Wilken.MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation b))
    (hβ : 1 < unionInterpretation b) (hbq : unionInterpretation b ≤ unionInterpretation q) :
    unionInterpretation b ≤ unionInterpretation c ∧ unionInterpretation c ≤ unionInterpretation q ∧
      unionInterpretation b ≤ Alexander313.Wilken.MultiplicativeNormalForm.lf (unionInterpretation c) := by
  have hs := truncate_value q b c hc
  have hq := (Principal.unionPrincipalCheck_exact q).mp hs.1
  rw [hs.2.2.2]
  exact ⟨Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_ge_source hq.2.1 hq.2.2 hm hβ hbq,
    Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_le hq.2.1 hq.2.2 _,
    Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_lf_ge_source hq.2.1 hq.2.2 hm hβ hbq⟩

theorem retainedForm_nonempty_source (q b : Nat) (rs : List Nat)
    (hr : Encodable.encode rs ∈ retainedForm q b)
    (hm : Alexander313.Wilken.MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (unionInterpretation b))
    (hβ : 1 < unionInterpretation b) (hbq : unionInterpretation b ≤ unionInterpretation q) : rs ≠ [] := by
  have hs := retainedForm_spec q b rs hr
  have hq := (Principal.unionPrincipalCheck_exact q).mp hs.1
  intro hz
  have hn := Alexander313.Wilken.MultiplicativeFactorTruncation.truncate_nonempty_source hq.2.1 hq.2.2 hm hβ hbq
  exact hn (hs.2.2.2.symm.trans (by rw [hz]; rfl))

/-- False selects the canonical product; true selects the encoded retained word. -/
def certificateOutput (word : Bool) (b d : Nat) : Nat :=
  cond word (encodeRetained b d) (productCode b d)

theorem certificateOutput_primrec : Primrec (fun p : Bool × (Nat × Nat) => certificateOutput p.1 p.2.1 p.2.2) :=
  Primrec.cond Primrec.fst
    (encodeRetained_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    (productCode_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

def certificateCheck (word : Bool) (query d : Nat) : Bool :=
  let input := query.unpair.1.unpair
  unionCheck input.2 && (PrincipalLogarithm.graph input.1 d &&
    (query.unpair.2 == certificateOutput word input.2 d))

theorem certificateCheck_primrec : Primrec (fun p : Bool × (Nat × Nat) => certificateCheck p.1 p.2.1 p.2.2) := by
  have hq : Primrec (fun p : Bool × (Nat × Nat) => p.2.1.unpair) := Primrec.unpair.comp (Primrec.fst.comp Primrec.snd)
  have hi := Primrec.unpair.comp (Primrec.fst.comp hq)
  have hd : Primrec (fun p : Bool × (Nat × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp (Uniform.unionCheck_primrec.comp (Primrec.snd.comp hi))
    (Primrec.and.comp (PrincipalLogarithm.graph_primrec.comp (Primrec.fst.comp hi) hd)
      (Primrec.beq.comp (Primrec.snd.comp hq)
        (certificateOutput_primrec.comp (Primrec.fst.pair ((Primrec.snd.comp hi).pair hd)))))

theorem truncateCertificate_exists_iff (q b c : Nat) :
    (∃ d, certificateCheck false (Nat.pair (Nat.pair q b) c) d = true) ↔ TruncateSpec q b c := by
  constructor
  · rintro ⟨d, hd⟩
    have hs : unionCheck b = true ∧ PrincipalLogarithm.graph q d = true ∧ c = productCode b d := by
      simpa only [certificateCheck, Nat.unpair_pair, certificateOutput, Bool.cond_false,
        Bool.and_eq_true, beq_iff_eq] using hd
    rw [hs.2.2]
    exact productCode_source q b d hs.1 hs.2.1
  · intro hs
    obtain ⟨d, hd⟩ := PrincipalLogarithm.graph_witness q hs.1
    have he := truncate_spec_unique q q b b c (productCode b d) hs (productCode_source q b d hs.2.1 hd) rfl rfl
    exact ⟨d, by simp only [certificateCheck, Nat.unpair_pair, hs.2.1, hd, Bool.true_and,
      certificateOutput, Bool.cond_false, beq_iff_eq]; exact he⟩

theorem retainedCertificate_exists_iff (q b c : Nat) :
    (∃ d, certificateCheck true (Nat.pair (Nat.pair q b) c) d = true) ↔
      ∃ rs : List Nat, c = Encodable.encode rs ∧ RetainedSpec q b rs := by
  constructor
  · rintro ⟨d, hd⟩
    have hs : unionCheck b = true ∧ PrincipalLogarithm.graph q d = true ∧ c = encodeRetained b d := by
      simpa only [certificateCheck, Nat.unpair_pair, certificateOutput, Bool.cond_true,
        Bool.and_eq_true, beq_iff_eq] using hd
    exact ⟨retainedWord b d, hs.2.2, retainedWord_spec q b d hs.1 hs.2.1⟩
  · rintro ⟨rs, rfl, hs⟩
    obtain ⟨d, hd⟩ := PrincipalLogarithm.graph_witness q hs.1
    have he := retained_spec_unique q q b b rs (retainedWord b d) hs (retainedWord_spec q b d hs.2.1 hd) rfl rfl
    exact ⟨d, by simp only [certificateCheck, Nat.unpair_pair, hs.2.1, hd, Bool.true_and,
      certificateOutput, Bool.cond_true, beq_iff_eq, encodeRetained, he]⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.FactorTruncation
