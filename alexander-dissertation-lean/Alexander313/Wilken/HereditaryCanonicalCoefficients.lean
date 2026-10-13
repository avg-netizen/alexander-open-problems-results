import Alexander313.Wilken.HereditaryCoefficientNormalForm
import Alexander313.Wilken.HereditaryFiniteMultiplication

/-!
# Unique actual additive coefficient data

Each genuine normalized principal atom of an original low source is tagged
with its real source level and canonicalized by the existing bounded least-code
algorithm. The resulting word consists of genuinely canonical union codes.
Literal Nat equality then compresses this word into positive coefficients.
The expanded values are the actual canonical ANF, and retained head values
strictly descend. Canonical head value injection proves equality of entire
words and coefficient lists for any two originally admitted sources of the
same actual ordinal, including sources at different finite levels.

Actual finite products and canonical sums reconstruct the unique canonical
source value. No uniqueness of raw tree spellings or supplied normal-form,
arithmetic, equality or effectivity oracle is used. These are numerical
canonical additive data, not the full printed theta/endpoint or multiplicative
forms. All proof terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.CanonicalCoefficients

abbrev Form := Coefficients.Runs Nat

def headCode (r : Nat) (a : RelativeTerm Nat) : Nat :=
  Canonical.canonicalize (Nat.pair r a.code)

theorem headCode_primrec : Primrec₂ headCode :=
  (Canonical.Effective.canonicalize_primrec.comp
    (Primrec₂.natPair.comp Primrec.fst (code_primrec.comp Primrec.snd))).to₂

theorem headCode_spec (r : Nat) (a : RelativeTerm Nat) (ha : lowCheckCode r a.code = true) :
    Canonical.check (headCode r a) = true ∧ unionInterpretation (headCode r a) = denote r a := by
  have htag : unionCheck (Nat.pair r a.code) = true := by
    simpa only [unionCheck_pair] using ha
  exact ⟨Canonical.canonicalize_check _ htag,
    (Canonical.canonicalize_value _ htag).trans (by simp only [unionInterpretation_pair, interpretation_code])⟩

def word (q : Nat) : List Nat :=
  (Principal.normalizedAtoms q.unpair.1 q.unpair.2).map (headCode q.unpair.1)

theorem word_primrec : Primrec word := by
  have hp := Primrec.unpair
  have hatoms := Principal.normalizedAtoms_primrec.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp)
  have hh : Primrec₂ (fun (q : Nat) (a : RelativeTerm Nat) => headCode q.unpair.1 a) :=
    (headCode_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)) Primrec.snd).to₂
  exact Primrec.list_map hatoms hh

private theorem canonical_coefficients_source_checked (q : Nat) (hq : unionCheck q = true) :
    checkCode q.unpair.1 q.unpair.2 = true :=
  (Bool.and_eq_true_iff.mp (by simpa only [unionCheck, lowCheckCode_eq] using hq)).1

theorem word_head_spec (q : Nat) (hq : unionCheck q = true) (c : Nat) (hc : c ∈ word q) :
    Canonical.check c = true ∧ 0 < unionInterpretation c ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation c) := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
  have hlow := Principal.normalizedAtoms_low q.unpair.1 q.unpair.2 hq a ha
  have hs := headCode_spec q.unpair.1 a hlow
  have hp := Principal.normalizedAtoms_admitted q.unpair.1 q.unpair.2
    (canonical_coefficients_source_checked q hq) a ha
  exact ⟨hs.1, by rw [hs.2]; exact hp.2.2⟩

theorem word_anf (q : Nat) (hq : unionCheck q = true) :
    (word q).map unionInterpretation = canonicalANF (unionInterpretation q) := by
  calc
    (word q).map unionInterpretation =
        (Principal.normalizedAtoms q.unpair.1 q.unpair.2).map (denote q.unpair.1) := by
      simp only [word, List.map_map]
      apply List.map_congr_left
      intro a ha
      exact (headCode_spec q.unpair.1 a
        (Principal.normalizedAtoms_low q.unpair.1 q.unpair.2 hq a ha)).2
    _ = canonicalANF (unionInterpretation q) :=
      Principal.normalizedAtoms_anf q.unpair.1 q.unpair.2 (canonical_coefficients_source_checked q hq)

theorem checked_word_ext (xs ys : List Nat)
    (hx : ∀ c ∈ xs, Canonical.check c = true)
    (hy : ∀ c ∈ ys, Canonical.check c = true)
    (he : xs.map unionInterpretation = ys.map unionInterpretation) : xs = ys := by
  revert hx hy he
  induction xs generalizing ys with
  | nil =>
    intro _ _ he
    cases ys with
    | nil => rfl
    | cons b bs => cases he
  | cons a as ih =>
    intro hx hy he
    cases ys with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at he
    | cons b bs =>
      have hm : unionInterpretation a = unionInterpretation b ∧
          as.map unionInterpretation = bs.map unionInterpretation := by
        simpa only [List.map_cons, List.cons.injEq] using he
      have hab := Canonical.check_value_injective a b (hx a List.mem_cons_self)
        (hy b List.mem_cons_self) hm.1
      have htail := ih bs (fun c hc => hx c (List.mem_cons_of_mem _ hc))
        (fun c hc => hy c (List.mem_cons_of_mem _ hc)) hm.2
      exact congrArg₂ List.cons hab htail

theorem word_invariant (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true)
    (he : unionInterpretation q = unionInterpretation v) : word q = word v := by
  apply checked_word_ext _ _
    (fun c hc => (word_head_spec q hq c hc).1) (fun c hc => (word_head_spec v hv c hc).1)
  rw [word_anf q hq, word_anf v hv, he]

private theorem canonical_coefficients_prepend_expansion (a : Nat) (rs : Form) :
    Coefficients.expand (Coefficients.prependRun (fun c d => c == d) a rs) =
      a :: Coefficients.expand rs := by
  cases rs with
  | nil => rfl
  | cons p rs =>
    rcases p with ⟨b, n⟩
    cases he : (a == b) with
    | false => simp only [Coefficients.prependRun, he, Bool.cond_false,
        Coefficients.expand, Coefficients.copies, List.cons_append, List.nil_append]
    | true =>
      have hab : a = b := beq_iff_eq.mp he
      subst b
      simp only [Coefficients.prependRun, he, Bool.cond_true,
        Coefficients.expand, Coefficients.copies, List.cons_append]

theorem literal_compress_expansion (xs : List Nat) :
    Coefficients.expand (Coefficients.compress (fun a b => a == b) xs) = xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [Coefficients.compress, canonical_coefficients_prepend_expansion, ih]

def form (q : Nat) : Form := Coefficients.compress (fun a b => a == b) (word q)

theorem form_primrec : Primrec form := by
  have he : Primrec (fun p : Unit × (Nat × Nat) => p.2.1 == p.2.2) :=
    Primrec.beq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (Coefficients.compress_primrec 0 (fun (_ : Unit) a b => a == b) he).comp
    ((Primrec.const ()).pair word_primrec)

theorem form_positive (q : Nat) : ∀ p ∈ form q, 0 < p.2 := Coefficients.compress_positive _ _

theorem form_head_mem (q : Nat) (p : Nat × Nat) (hp : p ∈ form q) : p.1 ∈ word q :=
  Coefficients.compress_head_mem _ _ p hp

theorem form_head_spec (q : Nat) (hq : unionCheck q = true) (p : Nat × Nat) (hp : p ∈ form q) :
    Canonical.check p.1 = true ∧ 0 < unionInterpretation p.1 ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation p.1) :=
  word_head_spec q hq p.1 (form_head_mem q p hp)

theorem form_head_original (q : Nat) (hq : unionCheck q = true) (p : Nat × Nat) (hp : p ∈ form q) :
    unionCheck p.1 = true := Canonical.check_original (form_head_spec q hq p hp).1

theorem form_head_normal (q : Nat) (hq : unionCheck q = true) (p : Nat × Nat) (hp : p ∈ form q) :
    Theta.Normal p.1.unpair.1 (ThetaCourse.rawTree p.1.unpair.2) :=
  Canonical.check_normal (form_head_spec q hq p hp).1

theorem form_expansion (q : Nat) : Coefficients.expand (form q) = word q := literal_compress_expansion _

theorem form_expansion_anf (q : Nat) (hq : unionCheck q = true) :
    (Coefficients.expand (form q)).map unionInterpretation = canonicalANF (unionInterpretation q) := by
  rw [form_expansion, word_anf q hq]

theorem form_descending (q : Nat) (hq : unionCheck q = true) :
    (form q).Pairwise (fun p s => unionInterpretation s.1 < unionInterpretation p.1) := by
  apply Coefficients.compress_descending _ unionInterpretation _
  · have hn := (canonicalANF_normal (unionInterpretation q)).2
    rw [← word_anf q hq] at hn
    simpa only [List.pairwise_map] using hn
  · intro a ha b hb
    rw [beq_iff_eq]
    constructor
    · intro he; rw [he]
    · exact Canonical.check_value_injective a b (word_head_spec q hq a ha).1
        (word_head_spec q hq b hb).1

theorem form_weighted_value (q : Nat) (hq : unionCheck q = true) :
    Coefficients.weightedSum unionInterpretation (form q) = unionInterpretation q := by
  rw [← Coefficients.expand_weightedSum, form_expansion_anf q hq, principalSum_canonicalANF]

theorem form_invariant (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true)
    (he : unionInterpretation q = unionInterpretation v) : form q = form v := by
  rw [form, form, word_invariant q v hq hv he]

theorem form_eq_iff (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    form q = form v ↔ unionInterpretation q = unionInterpretation v := by
  constructor
  · intro he
    rw [← form_weighted_value q hq, ← form_weighted_value v hv, he]
  · exact form_invariant q v hq hv

def encodeForm (q : Nat) : Nat := Encodable.encode (form q)

theorem encodeForm_primrec : Primrec encodeForm := Primrec.encode.comp form_primrec

theorem encodeForm_eq_iff (q v : Nat) (hq : unionCheck q = true) (hv : unionCheck v = true) :
    encodeForm q = encodeForm v ↔ unionInterpretation q = unionInterpretation v := by
  rw [encodeForm, encodeForm, Encodable.encode_injective.eq_iff, form_eq_iff q v hq hv]

def formEqual (q v : Nat) : Bool :=
  (unionCheck q && unionCheck v) && (encodeForm q == encodeForm v)

theorem formEqual_primrec : Primrec₂ formEqual :=
  (Primrec.and.comp
    (Primrec.and.comp (Uniform.unionCheck_primrec.comp Primrec.fst)
      (Uniform.unionCheck_primrec.comp Primrec.snd))
    (Primrec.beq.comp (encodeForm_primrec.comp Primrec.fst) (encodeForm_primrec.comp Primrec.snd))).to₂

theorem formEqual_exact (q v : Nat) : formEqual q v = true ↔
    unionCheck q = true ∧ unionCheck v = true ∧ unionInterpretation q = unionInterpretation v := by
  simp only [formEqual, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨hq, hv⟩, he⟩
    exact ⟨hq, hv, (encodeForm_eq_iff q v hq hv).mp he⟩
  · rintro ⟨hq, hv, he⟩
    exact ⟨⟨hq, hv⟩, (encodeForm_eq_iff q v hq hv).mpr he⟩

/-- Actual canonical reconstruction from the coefficients, respecting their order. -/
def reconstruct : Form → Nat
  | [] => Canonical.canonicalize Alexander313.HereditaryOrdinalLabels.zeroCode
  | (c, n) :: rs => CanonicalArithmetic.canonicalSum (FiniteMultiplication.multiplyCode c n) (reconstruct rs)

theorem reconstruct_primrec : Primrec reconstruct := by
  have hp : Primrec (fun p : Form × ((Nat × Nat) × Nat) => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hn : Primrec (fun p : Form × ((Nat × Nat) × Nat) => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hc : Primrec (fun p : Form × ((Nat × Nat) × Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hs := (CanonicalArithmetic.canonicalSum_primrec.comp
    (FiniteMultiplication.multiplyCode_primrec.comp hp hn) hc).to₂
  have h := Primrec.list_foldr Primrec.id
    (Primrec.const (Canonical.canonicalize Alexander313.HereditaryOrdinalLabels.zeroCode)) hs
  apply h.of_eq
  intro rs
  change rs.foldr
    (fun p c => CanonicalArithmetic.canonicalSum (FiniteMultiplication.multiplyCode p.1 p.2) c)
    (Canonical.canonicalize Alexander313.HereditaryOrdinalLabels.zeroCode) = reconstruct rs
  induction rs with
  | nil => rfl
  | cons p rs ih => cases p; simp only [List.foldr_cons, reconstruct, ih]

theorem reconstruct_checked (rs : Form) (hr : ∀ p ∈ rs, unionCheck p.1 = true) :
    Canonical.check (reconstruct rs) = true := by
  revert hr
  induction rs with
  | nil => intro _; exact Canonical.canonicalize_check _ Alexander313.HereditaryOrdinalLabels.zeroCode_checked
  | cons p rs ih =>
    intro hr
    rcases p with ⟨c, n⟩
    exact CanonicalArithmetic.canonicalSum_checked _ _
      (FiniteMultiplication.multiplyCode_original c n (hr (c, n) List.mem_cons_self))
      (Canonical.check_original (ih (fun p hp => hr p (List.mem_cons_of_mem _ hp))))

theorem reconstruct_value (rs : Form) (hr : ∀ p ∈ rs, unionCheck p.1 = true) :
    unionInterpretation (reconstruct rs) = Coefficients.weightedSum unionInterpretation rs := by
  revert hr
  induction rs with
  | nil =>
    intro _
    exact (Canonical.canonicalize_value _ Alexander313.HereditaryOrdinalLabels.zeroCode_checked).trans
      Alexander313.HereditaryOrdinalLabels.zeroCode_value
  | cons p rs ih =>
    intro hr
    rcases p with ⟨c, n⟩
    have ht := fun p hp => hr p (List.mem_cons_of_mem _ hp)
    rw [reconstruct, CanonicalArithmetic.canonicalSum_value _ _
      (FiniteMultiplication.multiplyCode_original c n (hr (c, n) List.mem_cons_self))
      (Canonical.check_original (reconstruct_checked rs ht)),
      FiniteMultiplication.multiplyCode_value c n (hr (c, n) List.mem_cons_self), ih ht]
    rfl

def reconstructCode (q : Nat) : Nat := reconstruct (form q)

theorem reconstructCode_primrec : Primrec reconstructCode := reconstruct_primrec.comp form_primrec

theorem reconstructCode_checked (q : Nat) (hq : unionCheck q = true) :
    Canonical.check (reconstructCode q) = true :=
  reconstruct_checked _ (fun p hp => form_head_original q hq p hp)

theorem reconstructCode_value (q : Nat) (hq : unionCheck q = true) :
    unionInterpretation (reconstructCode q) = unionInterpretation q :=
  (reconstruct_value _ (fun p hp => form_head_original q hq p hp)).trans (form_weighted_value q hq)

theorem reconstructCode_canonical (q : Nat) (hq : unionCheck q = true) :
    reconstructCode q = Canonical.canonicalize q :=
  Canonical.check_value_injective _ _ (reconstructCode_checked q hq) (Canonical.canonicalize_check q hq)
    ((reconstructCode_value q hq).trans (Canonical.canonicalize_value q hq).symm)

def graph (q c : Nat) : Bool := unionCheck q && (c == encodeForm q)

theorem graph_primrec : Primrec₂ graph :=
  (Primrec.and.comp (Uniform.unionCheck_primrec.comp Primrec.fst)
    (Primrec.beq.comp Primrec.snd (encodeForm_primrec.comp Primrec.fst))).to₂

theorem graph_exact (q c : Nat) : graph q c = true ↔ unionCheck q = true ∧ c = encodeForm q := by
  simp only [graph, Bool.and_eq_true, beq_iff_eq]

theorem graph_forms_exact (q : Nat) (rs : Form) : graph q (Encodable.encode rs) = true ↔
    unionCheck q = true ∧ rs = form q := by
  simp only [graph_exact, encodeForm, Encodable.encode_injective.eq_iff]

theorem graph_unique (q : Nat) (hq : unionCheck q = true) : ∃! c, graph q c = true := by
  refine ⟨encodeForm q, (graph_exact _ _).mpr ⟨hq, rfl⟩, ?_⟩
  intro c hc
  exact ((graph_exact q c).mp hc).2

theorem form_computable : Computable form := form_primrec.to_comp

end Alexander313.Wilken.RelativeTerm.Hereditary.CanonicalCoefficients
