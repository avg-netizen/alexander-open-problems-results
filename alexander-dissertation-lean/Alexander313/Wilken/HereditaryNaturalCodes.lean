import Alexander313.Wilken.HereditaryCanonicalArithmetic
import Alexander313.Wilken.HereditaryPrincipalClassification
import Alexander313.Wilken.HereditaryFiniteMultiplication

/-!
# Genuine finite ordinal recognition and numerical extraction

For an admitted finite value n, the actual normalized principal word has
length n. A real canonical graph comparison with the constructed
numeral of that length recognizes exactly finite ordinal values. The length
and checker are uniformly primitive recursive. No ordinal-to-Nat chooser,
semantic finite-value decision, or normalization oracle is supplied.
Recognized finite ordinal coefficients feed the genuine finite multiplication
algorithm, preserving both original code values. Malformed inputs stay outside
the correctness domain. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NaturalCodes

private theorem ones_normal (xs : List Ordinal.{0})
    (hx : ∀ a ∈ xs, a = 1) : IsAdditiveNormalForm xs := by
  refine ⟨?_, ?_⟩
  · intro a ha
    rw [hx a ha]
    refine ⟨zero_lt_one, ?_⟩
    simpa only [Ordinal.opow_zero] using
      Ordinal.isPrincipal_add_omega0_opow (0 : Ordinal.{0})
  · revert hx
    induction xs with
    | nil => intro _; exact List.Pairwise.nil
    | cons a xs ih =>
      intro hx
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih (fun b hb => hx b (List.mem_cons_of_mem a hb))⟩
      intro b hb
      simpa only [hx a List.mem_cons_self, hx b (List.mem_cons_of_mem a hb)] using
        (le_rfl : (1 : Ordinal.{0}) ≤ 1)

theorem canonicalANF_nat (n : Nat) :
    canonicalANF (n : Ordinal.{0}) = List.replicate n (1 : Ordinal.{0}) := by
  apply canonicalANF_eq_of_normal
    (ones_normal _ (fun _ ha => List.eq_of_mem_replicate ha))
  rw [principalSum_replicate, one_mul]

theorem canonicalANF_nat_length (n : Nat) :
    (canonicalANF (n : Ordinal.{0})).length = n := by
  rw [canonicalANF_nat, List.length_replicate]

def count (q : Nat) : Nat :=
  (Principal.normalizedAtoms q.unpair.1 q.unpair.2).length

theorem count_primrec : Primrec count :=
  Primrec.list_length.comp (Principal.normalizedAtoms_primrec.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))

private theorem union_checked (q : Nat) (hq : unionCheck q = true) :
    checkCode q.unpair.1 q.unpair.2 = true :=
  (Bool.and_eq_true_iff.mp (by simpa only [unionCheck, lowCheckCode_eq] using hq)).1

theorem count_eq_anf_length (q : Nat) (hq : unionCheck q = true) :
    count q = (canonicalANF (unionInterpretation q)).length :=
  Principal.normalizedAtoms_length q.unpair.1 q.unpair.2 (union_checked q hq)

theorem count_of_nat (q n : Nat) (hq : unionCheck q = true)
    (hv : unionInterpretation q = (n : Ordinal.{0})) : count q = n := by
  rw [count_eq_anf_length q hq, hv, canonicalANF_nat_length]

def check (q : Nat) : Bool :=
  Canonical.graph q (CanonicalArithmetic.numeralCode (count q))

theorem check_primrec : Primrec check :=
  Canonical.Effective.graph_primrec.comp Primrec.id
    (CanonicalArithmetic.numeralCode_primrec.comp count_primrec)

theorem check_value (q : Nat) : check q = true ↔
    unionCheck q = true ∧ unionInterpretation q = (count q : Ordinal.{0}) := by
  simp only [check, Canonical.graph_exact,
    CanonicalArithmetic.numeralCode_checked, CanonicalArithmetic.numeralCode_value, true_and]

theorem check_exact (q : Nat) : check q = true ↔
    unionCheck q = true ∧ ∃ n : Nat, unionInterpretation q = (n : Ordinal.{0}) := by
  constructor
  · intro h
    have hs := (check_value q).mp h
    exact ⟨hs.1, count q, hs.2⟩
  · rintro ⟨hq, n, hn⟩
    apply (check_value q).mpr
    exact ⟨hq, by rw [count_of_nat q n hq hn]; exact hn⟩

theorem check_below_omega (q : Nat) : check q = true ↔
    unionCheck q = true ∧ unionInterpretation q < Ordinal.omega0 := by
  rw [check_exact, Ordinal.lt_omega0]

theorem check_numeral (n : Nat) : check (CanonicalArithmetic.numeralCode n) = true :=
  (check_exact _).mpr ⟨Canonical.check_original (CanonicalArithmetic.numeralCode_checked n),
    n, CanonicalArithmetic.numeralCode_value n⟩

theorem count_numeral (n : Nat) : count (CanonicalArithmetic.numeralCode n) = n :=
  count_of_nat _ n (Canonical.check_original (CanonicalArithmetic.numeralCode_checked n))
    (CanonicalArithmetic.numeralCode_value n)

theorem count_invariant (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true)
    (he : unionInterpretation q = unionInterpretation v) : count q = count v := by
  rw [count_eq_anf_length q hq, count_eq_anf_length v hv, he]

theorem check_invariant (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true)
    (he : unionInterpretation q = unionInterpretation v) : check q = check v := by
  apply Bool.eq_iff_iff.mpr
  simp only [check_exact, hq, hv, true_and, he]

def extract (q : Nat) : Nat := cond (check q) (count q) 0

theorem extract_primrec : Primrec extract :=
  check_primrec.cond count_primrec (Primrec.const 0)

theorem extract_value (q : Nat) (hq : check q = true) :
    unionInterpretation q = (extract q : Ordinal.{0}) := by
  simpa only [extract, hq, Bool.cond_true] using ((check_value q).mp hq).2

theorem extract_of_nat (q n : Nat) (hq : unionCheck q = true)
    (hv : unionInterpretation q = (n : Ordinal.{0})) : extract q = n := by
  have hc : check q = true := (check_exact q).mpr ⟨hq, n, hv⟩
  simp only [extract, hc, Bool.cond_true, count_of_nat q n hq hv]

theorem extract_rejected (q : Nat) (hq : check q = false) : extract q = 0 := by
  simp only [extract, hq, Bool.cond_false]

theorem extracted_numeral_value (q : Nat) (hq : check q = true) :
    unionInterpretation (CanonicalArithmetic.numeralCode (extract q)) = unionInterpretation q :=
  (CanonicalArithmetic.numeralCode_value _).trans (extract_value q hq).symm

def graph (q n : Nat) : Bool := check q && (count q == n)

theorem graph_primrec : Primrec₂ graph :=
  (Primrec.and.comp (check_primrec.comp Primrec.fst)
    (Primrec.beq.comp (count_primrec.comp Primrec.fst) Primrec.snd)).to₂

theorem graph_exact (q n : Nat) : graph q n = true ↔
    unionCheck q = true ∧ unionInterpretation q = (n : Ordinal.{0}) := by
  simp only [graph, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hq, hn⟩
    have hs := (check_value q).mp hq
    exact ⟨hs.1, by rw [← hn]; exact hs.2⟩
  · rintro ⟨hq, hn⟩
    exact ⟨(check_exact q).mpr ⟨hq, n, hn⟩, count_of_nat q n hq hn⟩

theorem graph_unique (q : Nat) (hq : check q = true) : ∃! n : Nat, graph q n = true := by
  refine ⟨count q, by simp only [graph, hq, beq_self_eq_true, Bool.true_and], ?_⟩
  intro n hn
  exact (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hn).2).symm

/-- The finite coefficient is itself an original ordinal code. The checker
and extraction license this genuine finite branch of source multiplication. -/
def finiteInputs (q v : Nat) : Bool := unionCheck q && check v

theorem finiteInputs_primrec : Primrec₂ finiteInputs :=
  (Primrec.and.comp (Uniform.unionCheck_primrec.comp Primrec.fst)
    (check_primrec.comp Primrec.snd)).to₂

theorem finiteInputs_exact (q v : Nat) : finiteInputs q v = true ↔
    unionCheck q = true ∧ unionCheck v = true ∧ unionInterpretation v < Ordinal.omega0 := by
  simp only [finiteInputs, Bool.and_eq_true, check_below_omega]

def multiplyFinite (q v : Nat) : Nat :=
  cond (finiteInputs q v) (FiniteMultiplication.multiplyCode q (extract v)) 0

theorem multiplyFinite_primrec : Primrec₂ multiplyFinite :=
  (finiteInputs_primrec.cond
    (FiniteMultiplication.multiplyCode_primrec.comp Primrec.fst (extract_primrec.comp Primrec.snd))
      (Primrec.const 0)).to₂

theorem multiplyFinite_checked (q v : Nat) (hq : unionCheck q = true) (hv : check v = true) :
    Canonical.check (multiplyFinite q v) = true := by
  simpa only [multiplyFinite, finiteInputs, hq, hv, Bool.true_and, Bool.cond_true] using
    FiniteMultiplication.multiplyCode_checked q (extract v) hq

theorem multiplyFinite_value (q v : Nat) (hq : unionCheck q = true) (hv : check v = true) :
    unionInterpretation (multiplyFinite q v) = unionInterpretation q * unionInterpretation v := by
  simpa only [multiplyFinite, finiteInputs, hq, hv, Bool.true_and, Bool.cond_true,
    extract_value v hv] using FiniteMultiplication.multiplyCode_value q (extract v) hq

theorem multiplyFinite_rejected (q v : Nat) (h : finiteInputs q v = false) :
    multiplyFinite q v = 0 := by
  simp only [multiplyFinite, h, Bool.cond_false]

end Alexander313.Wilken.RelativeTerm.Hereditary.NaturalCodes
