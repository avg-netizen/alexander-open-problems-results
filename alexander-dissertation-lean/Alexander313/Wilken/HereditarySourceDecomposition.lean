import Alexander313.Wilken.HereditaryThetaNormalizationPrimitive
import Alexander313.Wilken.SourceHighPartComparison

/-!
# Executable original-source ANF and genuine cardinal decomposition

The actual hereditary principal-word algorithm at every public level supplies
canonical ANF values on its original admitted normal domain. A finite outer-sort
cut and genuine source reconstruction compute the cardinal high part and low
remainder, including the original level-zero/base-one case. Every output keeps
original admission, normality and the true source argument grammar. No ordinal
evaluation, public recoding or supplied partition oracle is used. Literal ANF
representatives may open earlier-level parameter payloads; source support is
not thereby identified with this comparison word. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceDecomposition

def inputCheck (r c : Nat) : Bool := Theta.acceptedCode r c

theorem inputCheck_primrec : Primrec₂ inputCheck := Theta.Effective.acceptedCode_primrec

theorem inputCheck_exact (r c : Nat) : inputCheck r c = true ↔
    checkCode r c = true ∧ Theta.Normal r (ThetaCourse.rawTree c) :=
  Theta.acceptedCode_iff r c

theorem input_tree (r c : Nat) (hc : inputCheck r c = true) :
    check r (ThetaCourse.rawTree c) = true ∧ Theta.Normal r (ThetaCourse.rawTree c) := by
  have hs := (inputCheck_exact r c).mp hc
  obtain ⟨t, ht, hct⟩ := (checkCode_iff r c).mp hs.1
  exact ⟨by simpa only [← ht, ThetaCourse.rawTree_code] using hct, hs.2⟩

theorem input_value (r c : Nat) (hc : inputCheck r c = true) :
    interpretation r c = denote r (ThetaCourse.rawTree c) := by
  obtain ⟨t, ht, hct⟩ := (checkCode_iff r c).mp ((inputCheck_exact r c).mp hc).1
  simp only [← ht, interpretation_code, ThetaCourse.rawTree_code]

def word (r c : Nat) : List (RelativeTerm Nat) := Theta.atoms r (ThetaCourse.rawTree c)

theorem word_primrec : Primrec₂ word :=
  (Theta.Effective.atoms_primrec.comp Primrec.fst (ThetaCourse.rawTree_primrec.comp Primrec.snd)).to₂

private theorem atoms_shape (r : Nat) (t a : RelativeTerm Nat) (ha : a ∈ Theta.atoms r t) :
    (∃ p, a = .parameter p) ∨ (∃ k b, a = .theta k b) := by
  revert ha
  induction t with
  | parameter p =>
    intro ha
    cases r with
    | zero => simp only [Theta.atoms_parameter_zero, List.not_mem_nil] at ha
    | succ r =>
      change a ∈ ((decode p).map (fun u =>
        (Theta.atoms r u).map (fun b => RelativeTerm.parameter b.code))).getD [] at ha
      cases hd : decode p with
      | none => simp only [hd, Option.map_none, Option.getD_none, List.not_mem_nil] at ha
      | some u =>
        simp only [hd, Option.map_some, Option.getD_some] at ha
        obtain ⟨b, hb, he⟩ := List.mem_map.mp ha
        exact Or.inl ⟨b.code, he.symm⟩
  | sum s t ihs iht =>
    intro ha
    rw [Theta.atoms_sum, List.mem_append] at ha
    exact ha.elim ihs iht
  | theta k b =>
    intro ha
    have he : a = .theta k b := by simpa only [Theta.atoms_theta, List.mem_singleton] using ha
    exact Or.inr ⟨k, b, he⟩

theorem word_shape (r c : Nat) (a : RelativeTerm Nat) (ha : a ∈ word r c) :
    (∃ p, a = .parameter p) ∨ (∃ k b, a = .theta k b) :=
  atoms_shape r (ThetaCourse.rawTree c) a ha

theorem word_spec (r c : Nat) (hc : inputCheck r c = true) :
    (∀ a ∈ word r c, check r a = true ∧ Theta.Normal r a ∧ 0 < denote r a ∧
      Ordinal.IsPrincipal (· + ·) (denote r a)) ∧
      (word r c).map (denote r) = canonicalANF (interpretation r c) := by
  have hs := input_tree r c hc
  let t := ThetaCourse.rawTree c
  let n := SourceOne.PublicCodes.fragment t
  have ht := Theta.checked_admissible r n t hs.1 (SourceOne.PublicCodes.height_le_fragment t)
  have ha := Theta.atoms_spec r n t ht hs.2
  have hn := Theta.atoms_denote_normal r n t ht hs.2
  refine ⟨?_, ?_⟩
  · intro a ham
    have haa := ha.1 a ham
    have hap := hn.1 (denote r a) (List.mem_map.mpr ⟨a, ham, rfl⟩)
    exact ⟨Theta.admitted_checked haa.1, haa.2, hap.1, hap.2⟩
  · rw [input_value r c hc]
    exact Theta.atoms_denote_anf r n t ht hs.2

theorem word_normal (r c : Nat) (hc : inputCheck r c = true) :
    IsAdditiveNormalForm ((word r c).map (denote r)) := by
  rw [(word_spec r c hc).2]
  exact canonicalANF_normal _

def above (m : Nat) (a : RelativeTerm Nat) : Bool := decide (m + 1 < a.outerSort)

theorem above_primrec : Primrec₂ above :=
  ((Primrec.nat_lt.comp (Primrec.succ.comp Primrec.fst) (outerSort_primrec.comp Primrec.snd)).decide).to₂

theorem above_exact (r m : Nat) (a : RelativeTerm Nat) (ha : check r a = true) :
    above m a = true ↔ omegaSequence (finiteBase r) (m + 1) ≤ denote r a := by
  rw [above, decide_eq_true_eq]
  have hs := denote_lt_iff_outerSort_le r a ha (m + 1) (Nat.succ_pos m)
  simpa only [not_le, not_lt] using (not_congr hs).symm

theorem below_exact (r m : Nat) (a : RelativeTerm Nat) (ha : check r a = true) :
    above m a = false ↔ denote r a < omegaSequence (finiteBase r) (m + 1) := by
  rw [above, Bool.decide_false_iff]
  simpa only [not_lt] using (denote_lt_iff_outerSort_le r a ha (m + 1) (Nat.succ_pos m)).symm

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

def highWord (r m c : Nat) : List (RelativeTerm Nat) := select true m (word r c)

def lowWord (r m c : Nat) : List (RelativeTerm Nat) := select false m (word r c)

theorem highWord_primrec : Primrec (fun p : Nat × (Nat × Nat) => highWord p.1 p.2.1 p.2.2) :=
  select_primrec.comp (((Primrec.const true).pair (Primrec.fst.comp Primrec.snd)).pair
    (word_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))

theorem lowWord_primrec : Primrec (fun p : Nat × (Nat × Nat) => lowWord p.1 p.2.1 p.2.2) :=
  select_primrec.comp (((Primrec.const false).pair (Primrec.fst.comp Primrec.snd)).pair
    (word_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))

theorem highWord_mem (r m c : Nat) (a : RelativeTerm Nat) :
    a ∈ highWord r m c ↔ a ∈ word r c ∧ above m a = true := by
  simpa only [highWord, Bool.cond_true] using select_mem true m (word r c) a

theorem lowWord_mem (r m c : Nat) (a : RelativeTerm Nat) :
    a ∈ lowWord r m c ↔ a ∈ word r c ∧ above m a = false := by
  have hs := select_mem false m (word r c) a
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

private theorem select_partition (r m : Nat) (as : List (RelativeTerm Nat))
    (ha : ∀ a ∈ as, check r a = true)
    (hn : (as.map (denote r)).Pairwise (fun a b => b ≤ a)) :
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
      have hab := (below_exact r m a (ha a List.mem_cons_self)).mp h
      have hbelow : ∀ b ∈ as, above m b = false := by
        intro b hb
        apply (below_exact r m b (ha b (List.mem_cons_of_mem _ hb))).mpr
        exact (hp.1 (denote r b) (List.mem_map.mpr ⟨b, hb, rfl⟩)).trans_lt hab
      have hs := select_below m as hbelow
      simp [select, h, hs.1, hs.2]

theorem word_partition (r m c : Nat) (hc : inputCheck r c = true) :
    word r c = highWord r m c ++ lowWord r m c :=
  select_partition r m (word r c) (fun a ha => ((word_spec r c hc).1 a ha).1) (word_normal r c hc).2

theorem highWord_bound (r m c : Nat) (hc : inputCheck r c = true) :
    ∀ a ∈ highWord r m c, omegaSequence (finiteBase r) (m + 1) ≤ denote r a := by
  intro a ha
  have hs := (highWord_mem r m c a).mp ha
  exact (above_exact r m a ((word_spec r c hc).1 a hs.1).1).mp hs.2

theorem lowWord_bound (r m c : Nat) (hc : inputCheck r c = true) :
    ∀ a ∈ lowWord r m c, denote r a < omegaSequence (finiteBase r) (m + 1) := by
  intro a ha
  have hs := (lowWord_mem r m c a).mp ha
  exact (below_exact r m a ((word_spec r c hc).1 a hs.1).1).mp hs.2

theorem words_normal (r m c : Nat) (hc : inputCheck r c = true) :
    IsAdditiveNormalForm ((highWord r m c).map (denote r)) ∧
      IsAdditiveNormalForm ((lowWord r m c).map (denote r)) := by
  have hn := word_normal r c hc
  rw [word_partition r m c hc, List.map_append] at hn
  have hp := List.pairwise_append.mp hn.2
  exact ⟨⟨fun a ha => hn.1 a (List.mem_append_left _ ha), hp.1⟩,
    ⟨fun a ha => hn.1 a (List.mem_append_right _ ha), hp.2.1⟩⟩

/-- All reconstructed pieces retain the very same original finite fragment. -/
theorem word_good (r n c : Nat) (hc : inputCheck r c = true)
    (hh : (ThetaCourse.rawTree c).height ≤ n) : Theta.Normalization.GoodAtoms r n (word r c) := by
  have hs := input_tree r c hc
  have ht := Theta.checked_admissible r n (ThetaCourse.rawTree c) hs.1 hh
  have ha := Theta.atoms_spec r n (ThetaCourse.rawTree c) ht hs.2
  have hn := word_normal r c hc
  intro a ham
  have haa := ha.1 a ham
  have hap := hn.1 _ (List.mem_map.mpr ⟨a, ham, rfl⟩)
  exact ⟨haa.1, haa.2, hap.1, hap.2⟩

theorem words_good (r n m c : Nat) (hc : inputCheck r c = true)
    (hh : (ThetaCourse.rawTree c).height ≤ n) :
    Theta.Normalization.GoodAtoms r n (highWord r m c) ∧ Theta.Normalization.GoodAtoms r n (lowWord r m c) := by
  have hw := word_good r n c hc hh
  exact ⟨fun a ha => hw a ((highWord_mem r m c a).mp ha).1,
    fun a ha => hw a ((lowWord_mem r m c a).mp ha).1⟩

def highPartTerm (r m c : Nat) : RelativeTerm Nat := Theta.Normalization.buildAtoms r (highWord r m c)

def lowPartTerm (r m c : Nat) : RelativeTerm Nat := Theta.Normalization.buildAtoms r (lowWord r m c)

def rebuildTerm (r c : Nat) : RelativeTerm Nat := Theta.Normalization.buildAtoms r (word r c)

def highCode (r m c : Nat) : Nat := (highPartTerm r m c).code

def lowCode (r m c : Nat) : Nat := (lowPartTerm r m c).code

def rebuildCode (r c : Nat) : Nat := (rebuildTerm r c).code

theorem highPartTerm_primrec : Primrec (fun p : Nat × (Nat × Nat) => highPartTerm p.1 p.2.1 p.2.2) :=
  Theta.Normalization.Effective.buildAtoms_primrec.comp Primrec.fst highWord_primrec

theorem lowPartTerm_primrec : Primrec (fun p : Nat × (Nat × Nat) => lowPartTerm p.1 p.2.1 p.2.2) :=
  Theta.Normalization.Effective.buildAtoms_primrec.comp Primrec.fst lowWord_primrec

theorem rebuildTerm_primrec : Primrec₂ rebuildTerm :=
  (Theta.Normalization.Effective.buildAtoms_primrec.comp Primrec.fst
    (word_primrec.comp Primrec.fst Primrec.snd)).to₂

theorem highCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => highCode p.1 p.2.1 p.2.2) :=
  code_primrec.comp highPartTerm_primrec

theorem lowCode_primrec : Primrec (fun p : Nat × (Nat × Nat) => lowCode p.1 p.2.1 p.2.2) :=
  code_primrec.comp lowPartTerm_primrec

theorem rebuildCode_primrec : Primrec₂ rebuildCode := code_primrec.comp₂ rebuildTerm_primrec

theorem parts_admissible (r n m c : Nat) (hc : inputCheck r c = true)
    (hh : (ThetaCourse.rawTree c).height ≤ n) :
    admissible r n (highPartTerm r m c) ∧ admissible r n (lowPartTerm r m c) := by
  have hs := words_good r n m c hc hh
  exact ⟨Theta.Normalization.buildAtoms_admissible r n _ hs.1,
    Theta.Normalization.buildAtoms_admissible r n _ hs.2⟩

theorem parts_normal (r m c : Nat) (hc : inputCheck r c = true) :
    Theta.Normal r (highPartTerm r m c) ∧ Theta.Normal r (lowPartTerm r m c) := by
  let n := SourceOne.PublicCodes.fragment (ThetaCourse.rawTree c)
  have hs := words_good r n m c hc (SourceOne.PublicCodes.height_le_fragment _)
  have hn := words_normal r m c hc
  exact ⟨Theta.Normalization.buildAtoms_normal r n _ hs.1 hn.1,
    Theta.Normalization.buildAtoms_normal r n _ hs.2 hn.2⟩

theorem parts_checked (r m c : Nat) (hc : inputCheck r c = true) :
    check r (highPartTerm r m c) = true ∧ check r (lowPartTerm r m c) = true := by
  let n := SourceOne.PublicCodes.fragment (ThetaCourse.rawTree c)
  have hs := parts_admissible r n m c hc (SourceOne.PublicCodes.height_le_fragment _)
  exact ⟨Theta.admitted_checked hs.1, Theta.admitted_checked hs.2⟩

theorem parts_accepted (r m c : Nat) (hc : inputCheck r c = true) :
    Theta.acceptedCode r (highCode r m c) = true ∧ Theta.acceptedCode r (lowCode r m c) = true := by
  have hs := parts_checked r m c hc
  have hn := parts_normal r m c hc
  constructor
  · apply (Theta.acceptedCode_iff r _).mpr
    exact ⟨by simpa only [highCode, checkCode_code] using hs.1,
      by simpa only [highCode, ThetaCourse.rawTree_code] using hn.1⟩
  · apply (Theta.acceptedCode_iff r _).mpr
    exact ⟨by simpa only [lowCode, checkCode_code] using hs.2,
      by simpa only [lowCode, ThetaCourse.rawTree_code] using hn.2⟩

theorem parts_word_values (r m c : Nat) :
    denote r (highPartTerm r m c) = principalSum ((highWord r m c).map (denote r)) ∧
      denote r (lowPartTerm r m c) = principalSum ((lowWord r m c).map (denote r)) :=
  ⟨Theta.Normalization.buildAtoms_denote r _, Theta.Normalization.buildAtoms_denote r _⟩

private theorem sum_dvd (Omega : Ordinal.{0}) (as : List Ordinal.{0})
    (ha : ∀ a ∈ as, Omega ∣ a) : Omega ∣ principalSum as := by
  revert ha
  induction as with
  | nil => exact fun ha => ⟨0, by simp only [principalSum, mul_zero]⟩
  | cons a as ih =>
    intro ha
    exact (Ordinal.dvd_add_iff (ha a List.mem_cons_self)).mpr
      (ih (fun b hb => ha b (List.mem_cons_of_mem _ hb)))

theorem parts_value (r m c : Nat) (hc : inputCheck r c = true) :
    denote r (highPartTerm r m c) = omegaSequence (finiteBase r) (m + 1) *
      (interpretation r c / omegaSequence (finiteBase r) (m + 1)) ∧
      denote r (lowPartTerm r m c) = interpretation r c % omegaSequence (finiteBase r) (m + 1) := by
  let Omega := omegaSequence (finiteBase r) (m + 1)
  let high := (highWord r m c).map (denote r)
  let low := (lowWord r m c).map (denote r)
  have hOmega : 0 < Omega := (omegaSequence_isSuccLimit (finiteBase r) m).bot_lt
  have hn := words_normal r m c hc
  have hlow : principalSum low < Omega := principalSum_lt hOmega (omegaSequence_add_closed (finiteBase r) m) low (by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    exact lowWord_bound r m c hc t ht)
  have hhigh : Omega ∣ principalSum high := sum_dvd Omega high (by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    exact SourceHighPartComparison.principal_dvd_of_le Omega (denote r t) hOmega
      (hn.1.1 _ (List.mem_map.mpr ⟨t, ht, rfl⟩)).2 (highWord_bound r m c hc t ht))
  obtain ⟨d, hd⟩ := hhigh
  have hv : interpretation r c = principalSum high + principalSum low := by
    rw [← principalSum_canonicalANF (interpretation r c), ← (word_spec r c hc).2,
      word_partition r m c hc, List.map_append, principalSum_append]
  have hdiv : interpretation r c / Omega = d := by
    rw [hv, hd, Ordinal.mul_add_div _ hOmega.ne', Ordinal.div_eq_zero_of_lt hlow, add_zero]
  have hmod : interpretation r c % Omega = principalSum low := by
    rw [hv, hd, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hlow]
  have hw := parts_word_values r m c
  exact ⟨hw.1.trans (by rw [hdiv, ← hd]), hw.2.trans hmod.symm⟩

theorem parts_code_value (r m c : Nat) (hc : inputCheck r c = true) :
    interpretation r (highCode r m c) = omegaSequence (finiteBase r) (m + 1) *
      (interpretation r c / omegaSequence (finiteBase r) (m + 1)) ∧
      interpretation r (lowCode r m c) = interpretation r c % omegaSequence (finiteBase r) (m + 1) := by
  simpa only [highCode, lowCode, interpretation_code] using parts_value r m c hc

theorem parts_anf (r m c : Nat) (hc : inputCheck r c = true) :
    (highWord r m c).map (denote r) = canonicalANF (interpretation r (highCode r m c)) ∧
      (lowWord r m c).map (denote r) = canonicalANF (interpretation r (lowCode r m c)) := by
  have hn := words_normal r m c hc
  have hv := parts_word_values r m c
  constructor
  · apply (canonicalANF_eq_of_normal hn.1 ?_).symm
    simpa only [highCode, interpretation_code] using hv.1.symm
  · apply (canonicalANF_eq_of_normal hn.2 ?_).symm
    simpa only [lowCode, interpretation_code] using hv.2.symm

theorem parts_reconstruct (r m c : Nat) (hc : inputCheck r c = true) :
    interpretation r (highCode r m c) + interpretation r (lowCode r m c) = interpretation r c := by
  rw [(parts_code_value r m c hc).1, (parts_code_value r m c hc).2]
  exact Ordinal.div_add_mod _ _

theorem lowPart_bound (r m c : Nat) (hc : inputCheck r c = true) :
    interpretation r (lowCode r m c) < omegaSequence (finiteBase r) (m + 1) := by
  rw [(parts_code_value r m c hc).2]
  exact Ordinal.mod_lt _ (omegaSequence_isSuccLimit (finiteBase r) m).bot_lt.ne'

theorem highPart_dvd (r m c : Nat) (hc : inputCheck r c = true) :
    omegaSequence (finiteBase r) (m + 1) ∣ interpretation r (highCode r m c) := by
  rw [(parts_code_value r m c hc).1]
  exact ⟨interpretation r c / omegaSequence (finiteBase r) (m + 1), rfl⟩

theorem lowPart_sort (r m c : Nat) (hc : inputCheck r c = true) :
    (lowPartTerm r m c).outerSort ≤ m + 1 := by
  apply (denote_lt_iff_outerSort_le r _ (parts_checked r m c hc).2 (m + 1) (Nat.succ_pos m)).mp
  simpa only [lowCode, interpretation_code] using lowPart_bound r m c hc

theorem parts_le (r m c : Nat) (hc : inputCheck r c = true) :
    interpretation r (highCode r m c) ≤ interpretation r c ∧
      interpretation r (lowCode r m c) ≤ interpretation r c := by
  rw [(parts_code_value r m c hc).1, (parts_code_value r m c hc).2]
  exact ⟨Ordinal.mul_div_le _ _, Ordinal.mod_le _ _⟩

theorem parts_sort (r m c : Nat) (hc : inputCheck r c = true)
    (hs : interpretation r c < omegaSequence (finiteBase r) (m + 2)) :
    denote r (highPartTerm r m c) < omegaSequence (finiteBase r) (m + 2) ∧
      denote r (lowPartTerm r m c) < omegaSequence (finiteBase r) (m + 2) := by
  have hl := parts_le r m c hc
  exact ⟨by simpa only [highCode, interpretation_code] using hl.1.trans_lt hs,
    by simpa only [lowCode, interpretation_code] using hl.2.trans_lt hs⟩

theorem rebuild_spec (r c : Nat) (hc : inputCheck r c = true) :
    Theta.acceptedCode r (rebuildCode r c) = true ∧
      interpretation r (rebuildCode r c) = interpretation r c := by
  let n := SourceOne.PublicCodes.fragment (ThetaCourse.rawTree c)
  have ha := word_good r n c hc (SourceOne.PublicCodes.height_le_fragment _)
  have had := Theta.Normalization.buildAtoms_admissible r n (word r c) ha
  have hnormal := Theta.Normalization.buildAtoms_normal r n (word r c) ha (word_normal r c hc)
  refine ⟨(Theta.acceptedCode_iff r _).mpr ⟨?_, ?_⟩, ?_⟩
  · simpa only [rebuildCode, rebuildTerm, checkCode_code] using Theta.admitted_checked had
  · simpa only [rebuildCode, rebuildTerm, ThetaCourse.rawTree_code] using hnormal
  · rw [rebuildCode, interpretation_code, rebuildTerm, Theta.Normalization.buildAtoms_denote,
      (word_spec r c hc).2, principalSum_canonicalANF]

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

theorem parts_sourceNotation (r n m c : Nat) (hc : inputCheck r c = true) (hm : m < n)
    (ha : sourceNotation (finiteBase r) n m (interpretation r c)) :
    sourceNotation (finiteBase r) n m (interpretation r (highCode r m c)) ∧
      sourceNotation (finiteBase r) n m (interpretation r (lowCode r m c)) := by
  have hv := parts_word_values r m c
  have hheads (a : RelativeTerm Nat) (ham : a ∈ word r c) : denote r a ∈ canonicalANF (interpretation r c) := by
    rw [← (word_spec r c hc).2]
    exact List.mem_map.mpr ⟨a, ham, rfl⟩
  constructor
  · rw [highCode, interpretation_code, hv.1]
    apply source_word_sum (finiteBase r) (finiteBase_pos r) n m hm _ ha
    intro a ham
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ham
    exact hheads t ((highWord_mem r m c t).mp ht).1
  · rw [lowCode, interpretation_code, hv.2]
    apply source_word_sum (finiteBase r) (finiteBase_pos r) n m hm _ ha
    intro a ham
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ham
    exact hheads t ((lowWord_mem r m c t).mp ht).1

/-- The original fragment suffices for the original same-level pieces;
their next-level admission is not substituted for this contract. -/
theorem parts_same_fragment_source (r n m c : Nat) (hc : inputCheck r c = true)
    (hh : (ThetaCourse.rawTree c).height ≤ n) (hm : m < n) :
    sourceNotation (finiteBase r) n m (interpretation r (highCode r m c)) ∧
      sourceNotation (finiteBase r) n m (interpretation r (lowCode r m c)) := by
  have ht := Theta.checked_admissible r n (ThetaCourse.rawTree c) (input_tree r c hc).1 hh
  have hn : 0 < n := (Nat.zero_le m).trans_lt hm
  have ha : sourceNotation (finiteBase r) n 0 (interpretation r c) := by
    rw [input_value r c hc, denote_eq_finite r n _ ht.2, sourceNotation, if_pos hn]
    exact ht.2.denote
  exact parts_sourceNotation r n m c hc hm
    (sourceNotation_upward (finiteBase r) n 0 m (Nat.zero_le m) hm.le ha)

theorem checked_all_levels (r m : Nat) (t : RelativeTerm Nat) (ht : check r t = true) :
    GlobalNotation (finiteBase r) m (denote r t) := by
  induction m with
  | zero => exact (globalNotation_iff_checked r _).mpr ⟨t, ht, rfl⟩
  | succ m ih => exact globalNotation_embeds_next (finiteBase r) (finiteBase_pos r) m ih

theorem parts_globalNotation (r m c : Nat) (hc : inputCheck r c = true) :
    GlobalNotation (finiteBase r) m (interpretation r (highCode r m c)) ∧
      GlobalNotation (finiteBase r) m (interpretation r (lowCode r m c)) := by
  have hs := parts_checked r m c hc
  exact ⟨by simpa only [highCode, interpretation_code] using checked_all_levels r m _ hs.1,
    by simpa only [lowCode, interpretation_code] using checked_all_levels r m _ hs.2⟩

theorem parts_values_invariant (r m c d : Nat) (hc : inputCheck r c = true) (hd : inputCheck r d = true)
    (he : interpretation r c = interpretation r d) :
    interpretation r (highCode r m c) = interpretation r (highCode r m d) ∧
      interpretation r (lowCode r m c) = interpretation r (lowCode r m d) := by
  rw [(parts_code_value r m c hc).1, (parts_code_value r m d hd).1,
    (parts_code_value r m c hc).2, (parts_code_value r m d hd).2, he]
  exact ⟨rfl, rfl⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceDecomposition
