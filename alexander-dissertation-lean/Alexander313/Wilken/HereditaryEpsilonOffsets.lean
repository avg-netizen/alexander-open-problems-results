import Alexander313.Wilken.HereditaryEpsilonClassification
import Alexander313.Wilken.HereditaryNaturalCodes
import Alexander313.Effective.HereditaryOrdinalFormation

/-!
# Genuine epsilon-plus-finite-offset decomposition

The actual normalized principal word is split at its first head. Its tail is
reconstructed in the original grammar and checked by the proved finite-value
recognizer. Its head is checked by the actual epsilon classifier, then genuinely
canonicalized. Real ANF uniqueness proves completeness and uniqueness for
xi = epsilon + n, with the literal omega fixed-point equation and raw natural n.
Executing strict-bound tests include the actual finite relativization base,
the epsilon-above-base branch of Wilken's corrected Lemma 2.41. No offset parser,
semantic class decision or code/value fidelity oracle is assumed. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EpsilonOffsets

open Theta ThetaCourse

theorem epsilon_pos_principal {ε : Ordinal.{0}} (hε : Ordinal.omega0 ^ ε = ε) :
    0 < ε ∧ Ordinal.IsPrincipal (· + ·) ε := by
  constructor
  · rw [← hε]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos
  · rw [← hε]
    exact Ordinal.isPrincipal_add_omega0_opow _

theorem epsilon_one_lt {ε : Ordinal.{0}} (hε : Ordinal.omega0 ^ ε = ε) : 1 < ε := by
  have h := omegaPower_strictMono (epsilon_pos_principal hε).1
  change Ordinal.omega0 ^ 0 < Ordinal.omega0 ^ ε at h
  rw [hε] at h
  simpa only [Ordinal.opow_zero] using h

/-- An epsilon followed by n genuine ones is already the unique actual ANF. -/
theorem canonicalANF_epsilon_add_nat {ε : Ordinal.{0}}
    (hε : Ordinal.omega0 ^ ε = ε) (n : Nat) :
    canonicalANF (ε + (n : Ordinal.{0})) = ε :: List.replicate n 1 := by
  have htail : IsAdditiveNormalForm (List.replicate n (1 : Ordinal.{0})) := by
    rw [← NaturalCodes.canonicalANF_nat]
    exact canonicalANF_normal _
  have hn : IsAdditiveNormalForm (ε :: List.replicate n (1 : Ordinal.{0})) := by
    refine ⟨?_, List.pairwise_cons.mpr ⟨?_, htail.2⟩⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact epsilon_pos_principal hε
      · exact htail.1 a ha
    · intro a ha
      rw [List.eq_of_mem_replicate ha]
      exact (epsilon_one_lt hε).le
  apply canonicalANF_eq_of_normal hn
  rw [principalSum, principalSum_replicate, one_mul]

/-- Equality of actual epsilon offsets forces both the real epsilon and the
raw natural offset to coincide. Raw source-tree spellings are not compared. -/
theorem epsilon_offset_unique {ε δ : Ordinal.{0}} {n m : Nat}
    (hε : Ordinal.omega0 ^ ε = ε) (hδ : Ordinal.omega0 ^ δ = δ)
    (he : ε + (n : Ordinal.{0}) = δ + (m : Ordinal.{0})) : ε = δ ∧ n = m := by
  have h := congrArg canonicalANF he
  rw [canonicalANF_epsilon_add_nat hε n, canonicalANF_epsilon_add_nat hδ m] at h
  have hs := List.cons.inj h
  exact ⟨hs.1, by simpa only [List.length_replicate] using congrArg List.length hs.2⟩

def word (q : Nat) : List (RelativeTerm Nat) :=
  Principal.normalizedAtoms q.unpair.1 q.unpair.2

theorem word_primrec : Primrec word :=
  Principal.normalizedAtoms_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)

private theorem union_checked (q : Nat) (hq : unionCheck q = true) :
    checkCode q.unpair.1 q.unpair.2 = true :=
  (Bool.and_eq_true_iff.mp (by simpa only [unionCheck, lowCheckCode_eq] using hq)).1

theorem word_anf (q : Nat) (hq : unionCheck q = true) :
    (word q).map (denote q.unpair.1) = canonicalANF (unionInterpretation q) :=
  Principal.normalizedAtoms_anf q.unpair.1 q.unpair.2 (union_checked q hq)

theorem word_value (q : Nat) (hq : unionCheck q = true) :
    principalSum ((word q).map (denote q.unpair.1)) = unionInterpretation q := by
  rw [word_anf q hq, principalSum_canonicalANF]

def headTree (q : Nat) : RelativeTerm Nat := (word q)[0]?.getD (.parameter 0)

theorem headTree_primrec : Primrec headTree :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp word_primrec (Primrec.const 0))
    (Primrec.const (RelativeTerm.parameter 0))

def tailTree (q : Nat) : RelativeTerm Nat := Normalization.buildAtoms q.unpair.1 (word q).tail

theorem tailTree_primrec : Primrec tailTree :=
  Normalization.Effective.buildAtoms_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.list_tail.comp word_primrec)

def rawHead (q : Nat) : Nat := Nat.pair q.unpair.1 (headTree q).code

theorem rawHead_primrec : Primrec rawHead :=
  Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair) (code_primrec.comp headTree_primrec)

def rawTail (q : Nat) : Nat := Nat.pair q.unpair.1 (tailTree q).code

theorem rawTail_primrec : Primrec rawTail :=
  Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair) (code_primrec.comp tailTree_primrec)

@[simp] theorem rawHead_value (q : Nat) :
    unionInterpretation (rawHead q) = denote q.unpair.1 (headTree q) := by
  simp only [rawHead, unionInterpretation, Nat.unpair_pair, interpretation_code]

@[simp] theorem rawTail_value (q : Nat) :
    unionInterpretation (rawTail q) = principalSum ((word q).tail.map (denote q.unpair.1)) := by
  simp only [rawTail, unionInterpretation, Nat.unpair_pair, interpretation_code,
    tailTree, Normalization.buildAtoms_denote]

private theorem tail_mem {α : Type} (xs : List α) {a : α} (ha : a ∈ xs.tail) : a ∈ xs := by
  cases xs with
  | nil => simp at ha
  | cons b bs => exact List.mem_cons_of_mem b ha

private theorem tail_sum_le {α : Type} (value : α → Ordinal.{0}) (xs : List α) :
    principalSum (xs.tail.map value) ≤ principalSum (xs.map value) := by
  cases xs with
  | nil => exact le_rfl
  | cons a as => exact le_add_self

theorem headTree_mem (q : Nat) (hnonempty : 0 < (word q).length) : headTree q ∈ word q := by
  cases hw : word q with
  | nil => simp only [hw, List.length_nil, Nat.lt_irrefl] at hnonempty
  | cons a as => simp [headTree, hw]

theorem rawHead_checked (q : Nat) (hq : unionCheck q = true)
    (hnonempty : 0 < (word q).length) : unionCheck (rawHead q) = true := by
  simpa only [rawHead, unionCheck, Nat.unpair_pair] using
    Principal.normalizedAtoms_low q.unpair.1 q.unpair.2 hq (headTree q) (headTree_mem q hnonempty)

theorem tailTree_spec (q : Nat) (hq : unionCheck q = true) :
    check q.unpair.1 (tailTree q) = true ∧ Normal q.unpair.1 (tailTree q) := by
  let r := q.unpair.1
  let t := Principal.normalizedTree r q.unpair.2
  let n := SourceOne.PublicCodes.fragment t
  have hs := Principal.normalizedTree_spec r q.unpair.2 (union_checked q hq)
  have ht : admissible r n t := (finiteCheck_iff r n t).mp hs.1
  have good : Normalization.GoodAtoms r n (word q).tail := by
    intro a ha
    exact Normalization.GoodAtoms.atoms r n t ht hs.2.1 a (tail_mem (word q) ha)
  have hn : IsAdditiveNormalForm ((word q).tail.map (denote r)) := by
    have hfull : IsAdditiveNormalForm ((word q).map (denote r)) := by
      rw [word_anf q hq]
      exact canonicalANF_normal _
    cases hw : word q with
    | nil => simpa only [hw, List.tail_nil, List.map_nil] using additiveNormalForm_nil
    | cons a as =>
      simp only [hw, List.map_cons] at hfull
      simpa only [hw, List.tail_cons] using additiveNormalForm_tail hfull
  exact ⟨admitted_checked (Normalization.buildAtoms_admissible r n _ good),
    Normalization.buildAtoms_normal r n _ good hn⟩

theorem rawTail_checked (q : Nat) (hq : unionCheck q = true) : unionCheck (rawTail q) = true := by
  have hs := tailTree_spec q hq
  have hle : denote q.unpair.1 (tailTree q) ≤ unionInterpretation q := by
    rw [tailTree, Normalization.buildAtoms_denote, ← word_value q hq]
    exact tail_sum_le (denote q.unpair.1) (word q)
  have hinput : unionInterpretation q < finiteBase (q.unpair.1 + 1) :=
    (lt_nextBase_iff_code q.unpair.1 _).mpr ⟨q.unpair.2, hq, rfl⟩
  have hsort := (denote_lt_iff_outerSort_le q.unpair.1 (tailTree q) hs.1 1
    (Nat.zero_lt_succ 0)).mp ((hle.trans_lt hinput).trans (finiteBase_lt_cardinal q.unpair.1))
  simpa only [rawTail, unionCheck, Nat.unpair_pair, lowCheckCode_code, lowCheck, hs.1,
    hsort, decide_true, Bool.true_and]

theorem raw_split (q : Nat) (hq : unionCheck q = true) (hnonempty : 0 < (word q).length) :
    unionInterpretation q = unionInterpretation (rawHead q) + unionInterpretation (rawTail q) := by
  rw [rawHead_value, rawTail_value]
  have hv := (word_value q hq).symm
  cases hw : word q with
  | nil => simp only [hw, List.length_nil, Nat.lt_irrefl] at hnonempty
  | cons a as => simpa [hw, headTree, principalSum] using hv

def head (q : Nat) : Nat := Canonical.canonicalize (rawHead q)

theorem head_primrec : Primrec head := Canonical.Effective.canonicalize_primrec.comp rawHead_primrec

def offset (q : Nat) : Nat := NaturalCodes.extract (rawTail q)

theorem offset_primrec : Primrec offset := NaturalCodes.extract_primrec.comp rawTail_primrec

def check (q : Nat) : Bool :=
  (unionCheck q && decide (0 < (word q).length)) &&
    (Epsilon.unionEpsilonCheck (rawHead q) && NaturalCodes.check (rawTail q))

theorem check_primrec : Primrec check :=
  Primrec.and.comp
    (Primrec.and.comp Uniform.unionCheck_primrec
      ((Primrec.nat_lt.comp (Primrec.const 0) (Primrec.list_length.comp word_primrec)).decide))
    (Primrec.and.comp (Epsilon.unionEpsilonCheck_primrec.comp rawHead_primrec)
      (NaturalCodes.check_primrec.comp rawTail_primrec))

theorem decomposition_spec (q : Nat) (hq : check q = true) :
    unionCheck q = true ∧ Canonical.check (head q) = true ∧
      Ordinal.omega0 ^ unionInterpretation (head q) = unionInterpretation (head q) ∧
      unionInterpretation q = unionInterpretation (head q) + (offset q : Ordinal.{0}) := by
  have hs := Bool.and_eq_true_iff.mp hq
  have hu := (Bool.and_eq_true_iff.mp hs.1).1
  have hp : 0 < (word q).length := of_decide_eq_true (Bool.and_eq_true_iff.mp hs.1).2
  have he := (Epsilon.unionEpsilonCheck_exact (rawHead q)).mp (Bool.and_eq_true_iff.mp hs.2).1
  have ht := (Bool.and_eq_true_iff.mp hs.2).2
  have hc : Canonical.check (head q) = true := Canonical.canonicalize_check _ he.1
  have hv : unionInterpretation (head q) = unionInterpretation (rawHead q) :=
    Canonical.canonicalize_value _ he.1
  refine ⟨hu, hc, by rw [hv]; exact he.2, ?_⟩
  rw [raw_split q hu hp, hv, NaturalCodes.extract_value (rawTail q) ht]
  rfl

/-- Completeness derives the first actual head and reconstructed tail from
ANF uniqueness. Neither parser success nor an offset witness is assumed. -/
theorem check_exact (q : Nat) : check q = true ↔ unionCheck q = true ∧
    ∃ ε : Ordinal.{0}, ∃ n : Nat, Ordinal.omega0 ^ ε = ε ∧
      unionInterpretation q = ε + (n : Ordinal.{0}) := by
  constructor
  · intro h
    have hs := decomposition_spec q h
    exact ⟨hs.1, unionInterpretation (head q), offset q, hs.2.2.1, hs.2.2.2⟩
  · rintro ⟨hq, ε, n, hε, hv⟩
    have hw := word_anf q hq
    rw [hv, canonicalANF_epsilon_add_nat hε n] at hw
    have hnonempty : 0 < (word q).length := by
      have hlength := congrArg List.length hw
      simp only [List.length_map, List.length_cons, List.length_replicate] at hlength
      omega
    have he : unionInterpretation (rawHead q) = ε := by
      rw [rawHead_value]
      cases hword : word q with
      | nil => simp [hword] at hw
      | cons a as =>
        simp only [hword, List.map_cons] at hw
        simpa [headTree, hword] using (List.cons.inj hw).1
    have ht : unionInterpretation (rawTail q) = (n : Ordinal.{0}) := by
      rw [rawTail_value]
      cases hword : word q with
      | nil => simp [hword] at hw
      | cons a as =>
        simp only [hword, List.map_cons] at hw
        rw [List.tail_cons, (List.cons.inj hw).2, principalSum_replicate, one_mul]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨hq, decide_eq_true_eq.mpr hnonempty⟩,
      Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · apply (Epsilon.unionEpsilonCheck_exact _).mpr
      exact ⟨rawHead_checked q hq hnonempty, by rw [he]; exact hε⟩
    · exact (NaturalCodes.check_exact _).mpr ⟨rawTail_checked q hq, n, ht⟩

theorem decomposition_unique (q : Nat) (hq : check q = true) (ε : Ordinal.{0}) (n : Nat)
    (hε : Ordinal.omega0 ^ ε = ε) (hv : unionInterpretation q = ε + (n : Ordinal.{0})) :
    unionInterpretation (head q) = ε ∧ offset q = n := by
  have hs := decomposition_spec q hq
  exact epsilon_offset_unique hs.2.2.1 hε (hs.2.2.2.symm.trans hv)

theorem decomposition_invariant (q v : Nat) (hq : check q = true) (hv : check v = true)
    (he : unionInterpretation q = unionInterpretation v) : head q = head v ∧ offset q = offset v := by
  have hq' := decomposition_spec q hq
  have hv' := decomposition_spec v hv
  have hu := decomposition_unique q hq (unionInterpretation (head v)) (offset v)
    hv'.2.2.1 (he.trans hv'.2.2.2)
  exact ⟨Canonical.check_value_injective _ _ hq'.2.1 hv'.2.1 hu.1, hu.2⟩

/-- Raw numeric output contains a genuine canonical epsilon code and a Nat. -/
def decompose (q : Nat) : Nat := cond (check q) (Nat.pair (head q) (offset q)) 0

theorem decompose_primrec : Primrec decompose :=
  check_primrec.cond (Primrec₂.natPair.comp head_primrec offset_primrec) (Primrec.const 0)

theorem decompose_checked (q : Nat) (hq : check q = true) :
    Canonical.check (decompose q).unpair.1 = true ∧
      Ordinal.omega0 ^ unionInterpretation (decompose q).unpair.1 =
        unionInterpretation (decompose q).unpair.1 ∧
      unionInterpretation q = unionInterpretation (decompose q).unpair.1 +
        ((decompose q).unpair.2 : Ordinal.{0}) := by
  simpa only [decompose, hq, Bool.cond_true, Nat.unpair_pair] using (decomposition_spec q hq).2

def graph (q c n : Nat) : Bool :=
  (check q && Canonical.check c) && ((head q == c) && (offset q == n))

theorem graph_primrec : Primrec (fun p : Nat × (Nat × Nat) => graph p.1 p.2.1 p.2.2) :=
  Primrec.and.comp
    (Primrec.and.comp (check_primrec.comp Primrec.fst)
      (Canonical.Effective.check_primrec.comp (Primrec.fst.comp Primrec.snd)))
    (Primrec.and.comp (Primrec.beq.comp (head_primrec.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
      (Primrec.beq.comp (offset_primrec.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))

theorem graph_exact (q c n : Nat) : graph q c n = true ↔
    unionCheck q = true ∧ Canonical.check c = true ∧
      Ordinal.omega0 ^ unionInterpretation c = unionInterpretation c ∧
      unionInterpretation q = unionInterpretation c + (n : Ordinal.{0}) := by
  simp only [graph, Bool.and_eq_true, beq_iff_eq, and_assoc]
  constructor
  · rintro ⟨hq, hc, he, hn⟩
    have hs := decomposition_spec q hq
    exact ⟨hs.1, hc, by rw [← he]; exact hs.2.2.1,
      by rw [← he, ← hn]; exact hs.2.2.2⟩
  · rintro ⟨hq, hc, hε, hv⟩
    have hcheck : check q = true := (check_exact q).mpr ⟨hq, unionInterpretation c, n, hε, hv⟩
    have hu := decomposition_unique q hcheck (unionInterpretation c) n hε hv
    exact ⟨hcheck, hc, Canonical.check_value_injective _ _ (decomposition_spec q hcheck).2.1 hc hu.1,
      hu.2⟩

theorem graph_unique (q : Nat) (hq : check q = true) :
    ∃! p : Nat × Nat, graph q p.1 p.2 = true := by
  have hs := decomposition_spec q hq
  refine ⟨(head q, offset q), ?_, ?_⟩
  · simp only [graph, hq, hs.2.1, beq_self_eq_true, Bool.true_and]
  · intro p hp
    simp only [graph, Bool.and_eq_true, beq_iff_eq] at hp
    apply Prod.ext
    · exact hp.2.1.symm
    · dsimp only
      have hsecond := hp.2.2.symm
      exact hsecond

/-- The supplied bound remains an original admitted ordinal code. -/
def aboveCheck (q b : Nat) : Bool := check q && HereditaryOrdinalFormation.unionLess b (head q)

theorem aboveCheck_primrec : Primrec₂ aboveCheck := by
  have h := (Primrec.and.comp (check_primrec.comp Primrec.fst)
    (HereditaryOrdinalFormation.unionLess_primrec.comp Primrec.snd
      (head_primrec.comp Primrec.fst))).to₂
  exact h.of_eq (fun _ _ => rfl)

theorem aboveCheck_exact (q b : Nat) : aboveCheck q b = true ↔
    unionCheck q = true ∧ unionCheck b = true ∧
      ∃ ε : Ordinal.{0}, ∃ n : Nat, Ordinal.omega0 ^ ε = ε ∧
        unionInterpretation b < ε ∧ unionInterpretation q = ε + (n : Ordinal.{0}) := by
  rw [aboveCheck, Bool.and_eq_true, HereditaryOrdinalFormation.unionLess_exact]
  constructor
  · rintro ⟨hq, hb, _, hbound⟩
    have hs := decomposition_spec q hq
    exact ⟨hs.1, hb, unionInterpretation (head q), offset q, hs.2.2.1, hbound, hs.2.2.2⟩
  · rintro ⟨hq, hb, ε, n, hε, hbound, hv⟩
    have hcheck : check q = true := (check_exact q).mpr ⟨hq, ε, n, hε, hv⟩
    have hu := decomposition_unique q hcheck ε n hε hv
    exact ⟨hcheck, hb, Canonical.check_original (decomposition_spec q hcheck).2.1,
      by rw [hu.1]; exact hbound⟩

/-- A literal originally admitted representation of the actual finite base. -/
def baseCode (r : Nat) : Nat := Nat.pair r (.theta 0 (zeroTree r) : RelativeTerm Nat).code

theorem baseCode_primrec : Primrec baseCode :=
  Primrec₂.natPair.comp Primrec.id (code_primrec.comp (theta_primrec.comp (Primrec.const 0)
    Normalization.Effective.zeroTree_primrec))

theorem baseCode_checked (r : Nat) : unionCheck (baseCode r) = true := by
  have hz := Normalization.zeroTree_admissible r 2
  have hsort : finiteDenote r 2 (zeroTree r) < omegaSequence (finiteBase r) 2 := by
    rw [← denote_eq_finite r 2 (zeroTree r) hz.2, zeroTree_denote]
    exact (finiteBase_pos r).trans_le
      ((omegaSequence_strictMono (finiteBase r)).monotone (Nat.zero_le 2))
  have ht : admissible r 2 (.theta 0 (zeroTree r)) :=
    ⟨hz.1, .theta le_rfl (by omega) hsort hz.2⟩
  simp only [baseCode, unionCheck, Nat.unpair_pair, lowCheckCode_code, lowCheck,
    admitted_checked ht, outerSort, Nat.zero_add, le_refl, decide_true, Bool.true_and]

theorem baseCode_value (r : Nat) : unionInterpretation (baseCode r) = finiteBase r := by
  simp only [baseCode, unionInterpretation, Nat.unpair_pair, interpretation_code]
  change globalCollapse (finiteBase r) 0 (denote r (zeroTree r)) = finiteBase r
  rw [zeroTree_denote, finiteBase_collapse_zero_base]

def aboveBaseCheck (r q : Nat) : Bool := aboveCheck q (baseCode r)

theorem aboveBaseCheck_primrec : Primrec₂ aboveBaseCheck :=
  (aboveCheck_primrec.comp Primrec.snd (baseCode_primrec.comp Primrec.fst)).to₂

/-- Exactly the literal epsilon-above-relativization-base condition used by
the corrected source Lemma 2.41, with the original input guard retained. -/
theorem aboveBaseCheck_exact (r q : Nat) : aboveBaseCheck r q = true ↔ unionCheck q = true ∧
    ∃ ε : Ordinal.{0}, ∃ n : Nat, Ordinal.omega0 ^ ε = ε ∧ finiteBase r < ε ∧
      unionInterpretation q = ε + (n : Ordinal.{0}) := by
  simp only [aboveBaseCheck, aboveCheck_exact, baseCode_checked, baseCode_value, true_and]

theorem check_computable : Computable check := check_primrec.to_comp

end Alexander313.Wilken.RelativeTerm.Hereditary.EpsilonOffsets
