import Alexander313.Wilken.HereditaryNativeComparison
import Alexander313.Wilken.HereditaryNativeNormalizationPrimitive
import Alexander313.Wilken.SourceHighPartComparison

/-!
# Executable native ANF and genuine cardinal decomposition

The original admitted weak-normal domain supplies the existing genuine native
principal word. The finite algorithm cuts that word at outer sort m+1, which
is proved equivalent to its actual ordinal cut at Omega_(m+1). Both native
outputs are reconstructed from the retained principal atoms; admission,
normality and ordinal division/remainder are derived, not supplied contracts.
Atomic public payloads remain atomic in literal source support. The word here
is the actual ANF comparison representative. No native ordinal evaluator or
public recoding oracle is used. All proof candidates are uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Decomposition

def inputCheck (q c : Nat) : Bool := Comparison.acceptedCode q c

theorem inputCheck_primrec : Primrec₂ inputCheck := Comparison.acceptedCode_primrec

theorem inputCheck_exact (q c : Nat) : inputCheck q c = true ↔
    checkCode q c = true ∧ Comparison.Normal q (ThetaCourse.rawTree c) :=
  Comparison.acceptedCode_exact q c

theorem input_tree (q c : Nat) (hc : inputCheck q c = true) :
    check q (ThetaCourse.rawTree c) = true ∧ Comparison.Normal q (ThetaCourse.rawTree c) := by
  have hs := (inputCheck_exact q c).mp hc
  obtain ⟨t, ht, hct⟩ := (checkCode_exact q c).mp hs.1
  exact ⟨by simpa only [← ht, ThetaCourse.rawTree_code] using hct, hs.2⟩

theorem input_value (q c : Nat) (hc : inputCheck q c = true) :
    interpretation q c = denote q (ThetaCourse.rawTree c) := by
  obtain ⟨t, ht, hct⟩ := (checkCode_exact q c).mp ((inputCheck_exact q c).mp hc).1
  simp only [← ht, interpretation_code, ThetaCourse.rawTree_code]

def word (c : Nat) : List (RelativeTerm Nat) := Comparison.atoms (ThetaCourse.rawTree c)

theorem word_primrec : Primrec word := Comparison.atoms_primrec.comp ThetaCourse.rawTree_primrec

theorem word_spec (q c : Nat) (hc : inputCheck q c = true) :
    (∀ a ∈ word c, check q a = true ∧ Comparison.Normal q a ∧ 0 < denote q a ∧
      Ordinal.IsPrincipal (· + ·) (denote q a)) ∧
      (word c).map (denote q) = canonicalANF (interpretation q c) := by
  have hs := input_tree q c hc
  have hq := (Bool.and_eq_true_iff.mp hs.1).1
  let t := ThetaCourse.rawTree c
  let n := SourceOne.PublicCodes.fragment t
  have ht := Comparison.checked_admissible q n t hs.1 (SourceOne.PublicCodes.height_le_fragment t)
  have ha := Comparison.atoms_spec q n hq t ht hs.2
  have hn := Comparison.atoms_normal q n hq t ht hs.2
  refine ⟨?_, ?_⟩
  · intro a ham
    have haa := ha.1 a ham
    have hap := hn.1 (denote q a) (List.mem_map.mpr ⟨a, ham, rfl⟩)
    exact ⟨Comparison.admitted_checked q n hq a haa.1, haa.2, hap.1, hap.2⟩
  · rw [input_value q c hc]
    exact Comparison.atoms_anf q n hq t ht hs.2

theorem word_normal (q c : Nat) (hc : inputCheck q c = true) :
    IsAdditiveNormalForm ((word c).map (denote q)) := by
  rw [(word_spec q c hc).2]
  exact canonicalANF_normal _

def above (m : Nat) (a : RelativeTerm Nat) : Bool := decide (m + 1 < a.outerSort)

theorem above_primrec : Primrec₂ above :=
  ((Primrec.nat_lt.comp (Primrec.succ.comp Primrec.fst) (outerSort_primrec.comp Primrec.snd)).decide).to₂

theorem above_exact (q m : Nat) (a : RelativeTerm Nat) (ha : check q a = true) :
    above m a = true ↔ omegaSequence (base q) (m + 1) ≤ denote q a := by
  rw [above, decide_eq_true_eq]
  have hs := denote_lt_iff_outerSort_le q a ha (m + 1) (Nat.succ_pos m)
  simpa only [not_le, not_lt] using (not_congr hs).symm

theorem below_exact (q m : Nat) (a : RelativeTerm Nat) (ha : check q a = true) :
    above m a = false ↔ denote q a < omegaSequence (base q) (m + 1) := by
  rw [above, Bool.decide_false_iff]
  simpa only [not_lt] using (denote_lt_iff_outerSort_le q a ha (m + 1) (Nat.succ_pos m)).symm

/-- An actual finite right fold, including both complementary cuts. -/
def select (high : Bool) (m : Nat) : List (RelativeTerm Nat) → List (RelativeTerm Nat)
  | [] => []
  | a :: as => cond (cond high (above m a) (!above m a)) (a :: select high m as) (select high m as)

theorem select_primrec : Primrec (fun p : (Bool × Nat) × List (RelativeTerm Nat) => select p.1.1 p.1.2 p.2) := by
  have hc : Primrec (fun p : ((Bool × Nat) × List (RelativeTerm Nat)) ×
      (RelativeTerm Nat × List (RelativeTerm Nat)) => above p.1.1.2 p.2.1) := above_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)
  have hk := (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).cond hc (Primrec.not.comp hc)
  have hs : Primrec₂ (fun p : (Bool × Nat) × List (RelativeTerm Nat) =>
      fun s : RelativeTerm Nat × List (RelativeTerm Nat) =>
        cond (cond p.1.1 (above p.1.2 s.1) (!above p.1.2 s.1)) (s.1 :: s.2) s.2) :=
    (hk.cond (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const []) hs
  have he : (fun p : (Bool × Nat) × List (RelativeTerm Nat) => p.2.foldr
      (fun a as => cond (cond p.1.1 (above p.1.2 a) (!above p.1.2 a)) (a :: as) as) []) =
      (fun p => select p.1.1 p.1.2 p.2) := by
    funext p
    rcases p with ⟨⟨high, m⟩, as⟩
    induction as with
    | nil => rfl
    | cons a as ih => simp only [List.foldr_cons, select, ih]
  rw [he] at h
  exact h

theorem select_filter (high : Bool) (m : Nat) (as : List (RelativeTerm Nat)) :
    select high m as = as.filter (fun a => cond high (above m a) (!above m a)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases h : cond high (above m a) (!above m a) <;> simp [select, h, ih]

theorem select_mem (high : Bool) (m : Nat) (as : List (RelativeTerm Nat)) (a : RelativeTerm Nat) :
    a ∈ select high m as ↔ a ∈ as ∧ cond high (above m a) (!above m a) = true := by
  rw [select_filter, List.mem_filter]

def highWord (m c : Nat) : List (RelativeTerm Nat) := select true m (word c)

def lowWord (m c : Nat) : List (RelativeTerm Nat) := select false m (word c)

theorem highWord_primrec : Primrec₂ highWord :=
  (select_primrec.comp (((Primrec.const true).pair Primrec.fst).pair (word_primrec.comp Primrec.snd))).to₂

theorem lowWord_primrec : Primrec₂ lowWord :=
  (select_primrec.comp (((Primrec.const false).pair Primrec.fst).pair (word_primrec.comp Primrec.snd))).to₂

theorem highWord_mem (m c : Nat) (a : RelativeTerm Nat) :
    a ∈ highWord m c ↔ a ∈ word c ∧ above m a = true := by
  simpa only [highWord, Bool.cond_true] using select_mem true m (word c) a

theorem lowWord_mem (m c : Nat) (a : RelativeTerm Nat) :
    a ∈ lowWord m c ↔ a ∈ word c ∧ above m a = false := by
  have hs := select_mem false m (word c) a
  cases h : above m a <;> simpa [lowWord, h] using hs

private theorem select_below (m : Nat) (as : List (RelativeTerm Nat))
    (ha : ∀ a ∈ as, above m a = false) : select true m as = [] ∧ select false m as = as := by
  revert ha
  induction as with
  | nil => exact fun ha => ⟨rfl, rfl⟩
  | cons a as ih =>
    intro ha
    have ht := ih (fun b hb => ha b (List.mem_cons_of_mem _ hb))
    simp [select, ha a List.mem_cons_self, ht.1, ht.2]

private theorem select_partition (q m : Nat) (as : List (RelativeTerm Nat))
    (ha : ∀ a ∈ as, check q a = true)
    (hn : (as.map (denote q)).Pairwise (fun a b => b ≤ a)) :
    as = select true m as ++ select false m as := by
  revert ha hn
  induction as with
  | nil => exact fun ha hn => rfl
  | cons a as ih =>
    intro ha hn
    have hp := List.pairwise_cons.mp hn
    have htail := ih (fun b hb => ha b (List.mem_cons_of_mem _ hb)) hp.2
    cases h : above m a with
    | true => simp [select, h, ← htail]
    | false =>
      have hab := (below_exact q m a (ha a List.mem_cons_self)).mp h
      have hbelow : ∀ b ∈ as, above m b = false := by
        intro b hb
        apply (below_exact q m b (ha b (List.mem_cons_of_mem _ hb))).mpr
        exact (hp.1 (denote q b) (List.mem_map.mpr ⟨b, hb, rfl⟩)).trans_lt hab
      have hs := select_below m as hbelow
      simp [select, h, hs.1, hs.2]

theorem word_partition (q m c : Nat) (hc : inputCheck q c = true) :
    word c = highWord m c ++ lowWord m c :=
  select_partition q m (word c) (fun a ha => ((word_spec q c hc).1 a ha).1) (word_normal q c hc).2

theorem highWord_bound (q m c : Nat) (hc : inputCheck q c = true) :
    ∀ a ∈ highWord m c, omegaSequence (base q) (m + 1) ≤ denote q a := by
  intro a ha
  have hs := (highWord_mem m c a).mp ha
  exact (above_exact q m a ((word_spec q c hc).1 a hs.1).1).mp hs.2

theorem lowWord_bound (q m c : Nat) (hc : inputCheck q c = true) :
    ∀ a ∈ lowWord m c, denote q a < omegaSequence (base q) (m + 1) := by
  intro a ha
  have hs := (lowWord_mem m c a).mp ha
  exact (below_exact q m a ((word_spec q c hc).1 a hs.1).1).mp hs.2

theorem words_normal (q m c : Nat) (hc : inputCheck q c = true) :
    IsAdditiveNormalForm ((highWord m c).map (denote q)) ∧
      IsAdditiveNormalForm ((lowWord m c).map (denote q)) := by
  have hn := word_normal q c hc
  rw [word_partition q m c hc, List.map_append] at hn
  have hp := List.pairwise_append.mp hn.2
  exact ⟨⟨fun a ha => hn.1 a (List.mem_append_left _ ha), hp.1⟩,
    ⟨fun a ha => hn.1 a (List.mem_append_right _ ha), hp.2.1⟩⟩

/-- All reconstructed pieces retain the very same original finite fragment. -/
theorem word_good (q n c : Nat) (hc : inputCheck q c = true)
    (hh : (ThetaCourse.rawTree c).height ≤ n) : Normalization.GoodAtoms q n (word c) := by
  have hs := input_tree q c hc
  have hq := (Bool.and_eq_true_iff.mp hs.1).1
  have ht := Comparison.checked_admissible q n (ThetaCourse.rawTree c) hs.1 hh
  have ha := Comparison.atoms_spec q n hq (ThetaCourse.rawTree c) ht hs.2
  have hn := word_normal q c hc
  intro a ham
  have haa := ha.1 a ham
  have hap := hn.1 _ (List.mem_map.mpr ⟨a, ham, rfl⟩)
  exact ⟨haa.1, haa.2, hap.1, hap.2⟩

theorem words_good (q n m c : Nat) (hc : inputCheck q c = true)
    (hh : (ThetaCourse.rawTree c).height ≤ n) :
    Normalization.GoodAtoms q n (highWord m c) ∧ Normalization.GoodAtoms q n (lowWord m c) := by
  have hw := word_good q n c hc hh
  exact ⟨fun a ha => hw a ((highWord_mem m c a).mp ha).1,
    fun a ha => hw a ((lowWord_mem m c a).mp ha).1⟩

def highPartTerm (m c : Nat) : RelativeTerm Nat := Normalization.buildAtoms (highWord m c)

def lowPartTerm (m c : Nat) : RelativeTerm Nat := Normalization.buildAtoms (lowWord m c)

def rebuildTerm (c : Nat) : RelativeTerm Nat := Normalization.buildAtoms (word c)

def highCode (m c : Nat) : Nat := (highPartTerm m c).code

def lowCode (m c : Nat) : Nat := (lowPartTerm m c).code

def rebuildCode (c : Nat) : Nat := (rebuildTerm c).code

theorem highPartTerm_primrec : Primrec₂ highPartTerm :=
  Normalization.Effective.buildAtoms_primrec.comp₂ highWord_primrec

theorem lowPartTerm_primrec : Primrec₂ lowPartTerm :=
  Normalization.Effective.buildAtoms_primrec.comp₂ lowWord_primrec

theorem rebuildTerm_primrec : Primrec rebuildTerm := Normalization.Effective.buildAtoms_primrec.comp word_primrec

theorem highCode_primrec : Primrec₂ highCode := code_primrec.comp₂ highPartTerm_primrec

theorem lowCode_primrec : Primrec₂ lowCode := code_primrec.comp₂ lowPartTerm_primrec

theorem rebuildCode_primrec : Primrec rebuildCode := code_primrec.comp rebuildTerm_primrec

theorem parts_admissible (q n m c : Nat) (hc : inputCheck q c = true)
    (hh : (ThetaCourse.rawTree c).height ≤ n) :
    admissible q n (highPartTerm m c) ∧ admissible q n (lowPartTerm m c) := by
  have hq := (Bool.and_eq_true_iff.mp (input_tree q c hc).1).1
  have hs := words_good q n m c hc hh
  exact ⟨Normalization.buildAtoms_admissible q n hq _ hs.1,
    Normalization.buildAtoms_admissible q n hq _ hs.2⟩

theorem parts_normal (q m c : Nat) (hc : inputCheck q c = true) :
    Comparison.Normal q (highPartTerm m c) ∧ Comparison.Normal q (lowPartTerm m c) := by
  let n := SourceOne.PublicCodes.fragment (ThetaCourse.rawTree c)
  have hs := words_good q n m c hc (SourceOne.PublicCodes.height_le_fragment _)
  have hn := words_normal q m c hc
  exact ⟨Normalization.buildAtoms_normal q n _ hs.1 hn.1,
    Normalization.buildAtoms_normal q n _ hs.2 hn.2⟩

theorem parts_checked (q m c : Nat) (hc : inputCheck q c = true) :
    check q (highPartTerm m c) = true ∧ check q (lowPartTerm m c) = true := by
  let n := SourceOne.PublicCodes.fragment (ThetaCourse.rawTree c)
  have hs := parts_admissible q n m c hc (SourceOne.PublicCodes.height_le_fragment _)
  have hq := (Bool.and_eq_true_iff.mp (input_tree q c hc).1).1
  exact ⟨Comparison.admitted_checked q n hq _ hs.1, Comparison.admitted_checked q n hq _ hs.2⟩

theorem parts_accepted (q m c : Nat) (hc : inputCheck q c = true) :
    Comparison.acceptedCode q (highCode m c) = true ∧ Comparison.acceptedCode q (lowCode m c) = true := by
  have hs := parts_checked q m c hc
  have hn := parts_normal q m c hc
  constructor
  · apply (Comparison.acceptedCode_exact q _).mpr
    exact ⟨by simpa only [highCode, checkCode_code] using hs.1,
      by simpa only [highCode, ThetaCourse.rawTree_code] using hn.1⟩
  · apply (Comparison.acceptedCode_exact q _).mpr
    exact ⟨by simpa only [lowCode, checkCode_code] using hs.2,
      by simpa only [lowCode, ThetaCourse.rawTree_code] using hn.2⟩

theorem parts_word_values (q m c : Nat) :
    denote q (highPartTerm m c) = principalSum ((highWord m c).map (denote q)) ∧
      denote q (lowPartTerm m c) = principalSum ((lowWord m c).map (denote q)) :=
  ⟨Normalization.buildAtoms_denote q _, Normalization.buildAtoms_denote q _⟩

private theorem sum_dvd (Omega : Ordinal.{0}) (as : List Ordinal.{0})
    (ha : ∀ a ∈ as, Omega ∣ a) : Omega ∣ principalSum as := by
  revert ha
  induction as with
  | nil => exact fun ha => ⟨0, by simp only [principalSum, mul_zero]⟩
  | cons a as ih =>
    intro ha
    exact (Ordinal.dvd_add_iff (ha a List.mem_cons_self)).mpr
      (ih (fun b hb => ha b (List.mem_cons_of_mem _ hb)))

theorem parts_value (q m c : Nat) (hc : inputCheck q c = true) :
    denote q (highPartTerm m c) = omegaSequence (base q) (m + 1) *
      (interpretation q c / omegaSequence (base q) (m + 1)) ∧
      denote q (lowPartTerm m c) = interpretation q c % omegaSequence (base q) (m + 1) := by
  let Omega := omegaSequence (base q) (m + 1)
  let high := (highWord m c).map (denote q)
  let low := (lowWord m c).map (denote q)
  have hOmega : 0 < Omega := (omegaSequence_isSuccLimit (base q) m).bot_lt
  have hn := words_normal q m c hc
  have hlow : principalSum low < Omega := principalSum_lt hOmega (omegaSequence_add_closed (base q) m) low (by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    exact lowWord_bound q m c hc t ht)
  have hhigh : Omega ∣ principalSum high := sum_dvd Omega high (by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    exact SourceHighPartComparison.principal_dvd_of_le Omega (denote q t) hOmega
      (hn.1.1 _ (List.mem_map.mpr ⟨t, ht, rfl⟩)).2 (highWord_bound q m c hc t ht))
  obtain ⟨d, hd⟩ := hhigh
  have hv : interpretation q c = principalSum high + principalSum low := by
    rw [← principalSum_canonicalANF (interpretation q c), ← (word_spec q c hc).2,
      word_partition q m c hc, List.map_append, principalSum_append]
  have hdiv : interpretation q c / Omega = d := by
    rw [hv, hd, Ordinal.mul_add_div _ hOmega.ne', Ordinal.div_eq_zero_of_lt hlow, add_zero]
  have hmod : interpretation q c % Omega = principalSum low := by
    rw [hv, hd, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hlow]
  have hw := parts_word_values q m c
  exact ⟨hw.1.trans (by rw [hdiv, ← hd]), hw.2.trans hmod.symm⟩

theorem parts_code_value (q m c : Nat) (hc : inputCheck q c = true) :
    interpretation q (highCode m c) = omegaSequence (base q) (m + 1) *
      (interpretation q c / omegaSequence (base q) (m + 1)) ∧
      interpretation q (lowCode m c) = interpretation q c % omegaSequence (base q) (m + 1) := by
  simpa only [highCode, lowCode, interpretation_code] using parts_value q m c hc

theorem parts_anf (q m c : Nat) (hc : inputCheck q c = true) :
    (highWord m c).map (denote q) = canonicalANF (interpretation q (highCode m c)) ∧
      (lowWord m c).map (denote q) = canonicalANF (interpretation q (lowCode m c)) := by
  have hn := words_normal q m c hc
  have hv := parts_word_values q m c
  constructor
  · apply (canonicalANF_eq_of_normal hn.1 ?_).symm
    simpa only [highCode, interpretation_code] using hv.1.symm
  · apply (canonicalANF_eq_of_normal hn.2 ?_).symm
    simpa only [lowCode, interpretation_code] using hv.2.symm

theorem parts_reconstruct (q m c : Nat) (hc : inputCheck q c = true) :
    interpretation q (highCode m c) + interpretation q (lowCode m c) = interpretation q c := by
  rw [(parts_code_value q m c hc).1, (parts_code_value q m c hc).2]
  exact Ordinal.div_add_mod _ _

theorem lowPart_bound (q m c : Nat) (hc : inputCheck q c = true) :
    interpretation q (lowCode m c) < omegaSequence (base q) (m + 1) := by
  rw [(parts_code_value q m c hc).2]
  exact Ordinal.mod_lt _ (omegaSequence_isSuccLimit (base q) m).bot_lt.ne'

theorem highPart_dvd (q m c : Nat) (hc : inputCheck q c = true) :
    omegaSequence (base q) (m + 1) ∣ interpretation q (highCode m c) := by
  rw [(parts_code_value q m c hc).1]
  exact ⟨interpretation q c / omegaSequence (base q) (m + 1), rfl⟩

theorem lowPart_sort (q m c : Nat) (hc : inputCheck q c = true) :
    (lowPartTerm m c).outerSort ≤ m + 1 := by
  apply (denote_lt_iff_outerSort_le q _ (parts_checked q m c hc).2 (m + 1) (Nat.succ_pos m)).mp
  simpa only [lowCode, interpretation_code] using lowPart_bound q m c hc

theorem parts_le (q m c : Nat) (hc : inputCheck q c = true) :
    interpretation q (highCode m c) ≤ interpretation q c ∧
      interpretation q (lowCode m c) ≤ interpretation q c := by
  rw [(parts_code_value q m c hc).1, (parts_code_value q m c hc).2]
  exact ⟨Ordinal.mul_div_le _ _, Ordinal.mod_le _ _⟩

theorem parts_sort (q m c : Nat) (hc : inputCheck q c = true)
    (hs : interpretation q c < omegaSequence (base q) (m + 2)) :
    denote q (highPartTerm m c) < omegaSequence (base q) (m + 2) ∧
      denote q (lowPartTerm m c) < omegaSequence (base q) (m + 2) := by
  have hl := parts_le q m c hc
  exact ⟨by simpa only [highCode, interpretation_code] using hl.1.trans_lt hs,
    by simpa only [lowCode, interpretation_code] using hl.2.trans_lt hs⟩

theorem rebuild_spec (q c : Nat) (hc : inputCheck q c = true) :
    Comparison.acceptedCode q (rebuildCode c) = true ∧
      interpretation q (rebuildCode c) = interpretation q c := by
  let n := SourceOne.PublicCodes.fragment (ThetaCourse.rawTree c)
  have hq := (Bool.and_eq_true_iff.mp (input_tree q c hc).1).1
  have ha := word_good q n c hc (SourceOne.PublicCodes.height_le_fragment _)
  have had := Normalization.buildAtoms_admissible q n hq (word c) ha
  have hnormal := Normalization.buildAtoms_normal q n (word c) ha (word_normal q c hc)
  refine ⟨(Comparison.acceptedCode_exact q _).mpr ⟨?_, ?_⟩, ?_⟩
  · simpa only [rebuildCode, rebuildTerm, checkCode_code] using Comparison.admitted_checked q n hq _ had
  · simpa only [rebuildCode, rebuildTerm, ThetaCourse.rawTree_code] using hnormal
  · rw [rebuildCode, interpretation_code, rebuildTerm, Normalization.buildAtoms_denote,
      (word_spec q c hc).2, principalSum_canonicalANF]

/-- Actual ANF hull inversion preserves the original source grammar of
every retained atom, including the same-level argument grammar. -/
private theorem source_word_sum (tau : Ordinal.{0}) (htau : 0 < tau)
    (n m : Nat) (hm : m < n) (a : Ordinal.{0}) (ha : sourceNotation tau n m a)
    (xs : List Ordinal.{0}) (hx : ∀ x ∈ xs, x ∈ canonicalANF a) :
    sourceNotation tau n m (principalSum xs) := by
  have hh := (sourceNotation_iff_hull tau n m hm a).mp ha
  have hs := (source_hull_iff_canonicalANF tau htau n m hm (omegaSequence tau (m + 2)) 0 a).mp hh
  apply (sourceNotation_iff_hull tau n m hm _).mpr
  revert hx
  induction xs with
  | nil =>
    intro hx
    exact .below_base (htau.trans_le ((omegaSequence_strictMono tau).monotone (Nat.zero_le m)))
  | cons x xs ih =>
    intro hx
    exact .add (hs x (hx x List.mem_cons_self))
      (ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)))

theorem parts_sourceNotation (q n m c : Nat) (hc : inputCheck q c = true) (hm : m < n)
    (ha : sourceNotation (base q) n m (interpretation q c)) :
    sourceNotation (base q) n m (interpretation q (highCode m c)) ∧
      sourceNotation (base q) n m (interpretation q (lowCode m c)) := by
  have hq := (Bool.and_eq_true_iff.mp (input_tree q c hc).1).1
  have hv := parts_word_values q m c
  have hheads (a : RelativeTerm Nat) (ham : a ∈ word c) : denote q a ∈ canonicalANF (interpretation q c) := by
    rw [← (word_spec q c hc).2]
    exact List.mem_map.mpr ⟨a, ham, rfl⟩
  constructor
  · rw [highCode, interpretation_code, hv.1]
    apply source_word_sum (base q) (base_pos q hq) n m hm _ ha
    intro a ham
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ham
    exact hheads t ((highWord_mem m c t).mp ht).1
  · rw [lowCode, interpretation_code, hv.2]
    apply source_word_sum (base q) (base_pos q hq) n m hm _ ha
    intro a ham
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ham
    exact hheads t ((lowWord_mem m c t).mp ht).1

/-- The original fragment suffices for the original same-level pieces;
their next-level admission is not substituted for this contract. -/
theorem parts_same_fragment_source (q n m c : Nat) (hc : inputCheck q c = true)
    (hh : (ThetaCourse.rawTree c).height ≤ n) (hm : m < n) :
    sourceNotation (base q) n m (interpretation q (highCode m c)) ∧
      sourceNotation (base q) n m (interpretation q (lowCode m c)) := by
  have hq := (Bool.and_eq_true_iff.mp (input_tree q c hc).1).1
  have ht := Comparison.checked_admissible q n (ThetaCourse.rawTree c) (input_tree q c hc).1 hh
  have hn : 0 < n := (Nat.zero_le m).trans_lt hm
  have ha : sourceNotation (base q) n 0 (interpretation q c) := by
    rw [input_value q c hc, denote_eq_finite q n hq _ ht.2, sourceNotation, if_pos hn]
    exact ht.2.denote
  exact parts_sourceNotation q n m c hc hm
    (sourceNotation_upward (base q) n 0 m (Nat.zero_le m) hm.le ha)

theorem checked_all_levels (q m : Nat) (t : RelativeTerm Nat) (ht : check q t = true) :
    GlobalNotation (base q) m (denote q t) := by
  have hq := (Bool.and_eq_true_iff.mp ht).1
  induction m with
  | zero => exact checked_globalNotation q t ht
  | succ m ih => exact globalNotation_embeds_next (base q) (base_pos q hq) m ih

theorem parts_globalNotation (q m c : Nat) (hc : inputCheck q c = true) :
    GlobalNotation (base q) m (interpretation q (highCode m c)) ∧
      GlobalNotation (base q) m (interpretation q (lowCode m c)) := by
  have hs := parts_checked q m c hc
  exact ⟨by simpa only [highCode, interpretation_code] using checked_all_levels q m _ hs.1,
    by simpa only [lowCode, interpretation_code] using checked_all_levels q m _ hs.2⟩

theorem parts_values_invariant (q m c d : Nat) (hc : inputCheck q c = true) (hd : inputCheck q d = true)
    (he : interpretation q c = interpretation q d) :
    interpretation q (highCode m c) = interpretation q (highCode m d) ∧
      interpretation q (lowCode m c) = interpretation q (lowCode m d) := by
  rw [(parts_code_value q m c hc).1, (parts_code_value q m d hd).1,
    (parts_code_value q m c hc).2, (parts_code_value q m d hd).2, he]
  exact ⟨rfl, rfl⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.Decomposition
