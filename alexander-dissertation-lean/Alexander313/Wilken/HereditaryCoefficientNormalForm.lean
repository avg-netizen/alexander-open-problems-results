import Alexander313.Wilken.HereditaryPrincipalClassification

/-!
# Executing coefficient compression of genuine hereditary principal words

The actual hereditary equality decision merges adjacent equal principal values
in the actual normalized atom list. It retains the first literal head, gives
every run a positive natural coefficient, and derives strictly descending head
values from the genuine additive normal form. Repeated equal values need not
have identical source spellings: expansion recovers the exact interpreted list.
Every retained head is an originally admitted normal atom, and low admission is
retained on the old low domain. Actual source reconstruction has the original
value and normality. All list operations are uniformly primitive recursive.

This supports additive coefficient forms. It does not construct epsilon or
multiplicative normal forms, printed theta indices, tracking or resemblance.
All proof terms remain uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Coefficients

abbrev Runs (α : Type) := List (α × Nat)

def copies {α : Type*} : Nat → α → List α
  | 0, _ => []
  | n + 1, a => a :: copies n a

theorem copies_replicate {α : Type*} (n : Nat) (a : α) : copies n a = List.replicate n a := by
  induction n <;> simp_all [copies, List.replicate_succ]

theorem copies_map {α : Type*} {β : Type*} (f : α → β) (n : Nat) (a : α) :
    (copies n a).map f = copies n (f a) := by
  induction n <;> simp_all [copies]

theorem copies_primrec {α : Type} [Primcodable α] : Primrec₂ (copies (α := α)) := by
  have hr := Primrec.nat_rec (Primrec.const ([] : List α))
      ((Primrec.list_cons.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂)
  have h : Primrec₂ (fun (a : α) n => copies n a) := hr.of_eq (by
    intro a n
    induction n <;> simp_all [copies])
  exact (h.comp Primrec.snd Primrec.fst).to₂

theorem copies_mem {α : Type*} (n : Nat) (a b : α) (h : b ∈ copies n a) : b = a := by
  induction n with
  | zero => simp [copies] at h
  | succ n ih =>
    rcases List.mem_cons.mp h with h | h
    · exact h
    · exact ih h

def expand {α : Type} : Runs α → List α
  | [] => []
  | (a, n) :: rs => copies n a ++ expand rs

theorem expand_primrec {α : Type} [Primcodable α] : Primrec (expand (α := α)) := by
  have hs : Primrec₂ (fun (_ : Runs α) => fun p : (α × Nat) × List α =>
      copies p.1.2 p.1.1 ++ p.2) :=
    (Primrec.list_append.comp
      (copies_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.id (Primrec.const []) hs
  have heq : (fun rs : Runs α =>
      rs.foldr (fun p as => copies p.2 p.1 ++ as) []) = expand := by
    funext rs
    induction rs with
    | nil => rfl
    | cons p rs ih => cases p; simp only [List.foldr_cons, expand, ih]
  exact h.of_eq (fun p => congrFun heq p)

theorem expand_mem {α : Type} (rs : Runs α) (a : α) (ha : a ∈ expand rs) :
    ∃ p ∈ rs, a = p.1 := by
  induction rs with
  | nil => simp [expand] at ha
  | cons p rs ih =>
    rcases List.mem_append.mp ha with ha | ha
    · exact ⟨p, List.mem_cons_self, copies_mem p.2 p.1 a ha⟩
    · obtain ⟨q, hq, he⟩ := ih ha
      exact ⟨q, List.mem_cons_of_mem _ hq, he⟩

def prependRun {α : Type} (equal : α → α → Bool) (a : α) : Runs α → Runs α
  | [] => [(a, 1)]
  | (b, n) :: rs =>
      cond (equal a b) ((a, n + 1) :: rs) ((a, 1) :: (b, n) :: rs)

def compress {α : Type} (equal : α → α → Bool) : List α → Runs α
  | [] => []
  | a :: as => prependRun equal a (compress equal as)

theorem compress_first_head {α : Type} (equal : α → α → Bool) (a : α) (as : List α) :
    ∃ n rs, compress equal (a :: as) = (a, n) :: rs := by
  cases hs : compress equal as with
  | nil => exact ⟨1, [], by simp only [compress, hs, prependRun]⟩
  | cons p rs =>
    rcases p with ⟨b, n⟩
    cases he : equal a b with
    | true => exact ⟨n + 1, rs, by simp only [compress, hs, prependRun, he, Bool.cond_true]⟩
    | false => exact ⟨1, (b, n) :: rs, by simp only [compress, hs, prependRun, he, Bool.cond_false]⟩

private def prependNumeric {α : Type} (default : α) (equal : α → α → Bool)
    (a : α) (rs : Runs α) : Runs α :=
  let p := rs[0]?.getD (default, 0)
  cond (rs.length == 0) [(a, 1)]
    (cond (equal a p.1) ((a, p.2 + 1) :: rs.tail) ((a, 1) :: rs))

theorem prependRun_primrec {α Data : Type} [Primcodable α] [Primcodable Data]
    (default : α) (equal : Data → α → α → Bool)
    (he : Primrec (fun p : Data × (α × α) => equal p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Data × (α × Runs α) => prependRun (equal p.1) p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Data × (α × Runs α) => p.1) := Primrec.fst
  have ha : Primrec (fun p : Data × (α × Runs α) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hrs : Primrec (fun p : Data × (α × Runs α) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hhead := Primrec.option_getD.comp
    (Primrec.list_getElem?.comp hrs (Primrec.const 0)) (Primrec.const (default, 0))
  have hsingle := Primrec.list_cons.comp (ha.pair (Primrec.const 1)) (Primrec.const [])
  have hmerged := Primrec.list_cons.comp
    (ha.pair (Primrec.succ.comp (Primrec.snd.comp hhead))) (Primrec.list_tail.comp hrs)
  have h := (Primrec.beq.comp (Primrec.list_length.comp hrs) (Primrec.const 0)).cond hsingle
    ((he.comp (hd.pair (ha.pair (Primrec.fst.comp hhead)))).cond hmerged
      (Primrec.list_cons.comp (ha.pair (Primrec.const 1)) hrs))
  have heq : (fun p : Data × (α × Runs α) => prependNumeric default (equal p.1) p.2.1 p.2.2) =
      (fun p : Data × (α × Runs α) => prependRun (equal p.1) p.2.1 p.2.2) := by
    funext p
    cases p.2.2 with
    | nil => simp [prependNumeric, prependRun]
    | cons q rs => cases q; simp [prependNumeric, prependRun]
  change Primrec (fun p : Data × (α × Runs α) => prependNumeric default (equal p.1) p.2.1 p.2.2) at h
  exact h.of_eq (fun p => congrFun heq p)

theorem compress_primrec {α Data : Type} [Primcodable α] [Primcodable Data]
    (default : α) (equal : Data → α → α → Bool)
    (he : Primrec (fun p : Data × (α × α) => equal p.1 p.2.1 p.2.2)) :
    Primrec (fun p : Data × List α => compress (equal p.1) p.2) := by
  have hs : Primrec₂ (fun p : Data × List α => fun q : α × Runs α =>
      prependRun (equal p.1) q.1 q.2) :=
    ((prependRun_primrec default equal he).comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  have h := Primrec.list_foldr Primrec.snd (Primrec.const []) hs
  have heq : (fun p : Data × List α => p.2.foldr (prependRun (equal p.1)) []) =
      (fun p : Data × List α => compress (equal p.1) p.2) := by
    funext p
    induction p.2 <;> simp_all only [List.foldr_nil, List.foldr_cons, compress]
  exact h.of_eq (fun p => congrFun heq p)

theorem prependRun_head_mem {α : Type} (equal : α → α → Bool) (a : α)
    (rs : Runs α) (p : α × Nat) (hp : p ∈ prependRun equal a rs) :
    p.1 = a ∨ p ∈ rs := by
  cases rs with
  | nil =>
    have he : p = (a, 1) := by simpa [prependRun] using hp
    exact Or.inl (congrArg Prod.fst he)
  | cons q rs =>
    rcases q with ⟨b, n⟩
    cases he : equal a b with
    | true =>
      have hm : p = (a, n + 1) ∨ p ∈ rs := by simpa [prependRun, he] using hp
      rcases hm with rfl | hm
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ hm)
    | false =>
      have hm : p = (a, 1) ∨ p ∈ (b, n) :: rs := by simpa [prependRun, he] using hp
      rcases hm with rfl | hm
      · exact Or.inl rfl
      · exact Or.inr hm

theorem compress_head_mem {α : Type} (equal : α → α → Bool) (as : List α)
    (p : α × Nat) (hp : p ∈ compress equal as) : p.1 ∈ as := by
  induction as with
  | nil => simp [compress] at hp
  | cons a as ih =>
    rcases prependRun_head_mem equal a _ p hp with he | hm
    · rw [he]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hm)

theorem compress_positive {α : Type} (equal : α → α → Bool) (as : List α) :
    ∀ p ∈ compress equal as, 0 < p.2 := by
  induction as with
  | nil => simp [compress]
  | cons a as ih =>
    cases hs : compress equal as with
    | nil => simp [compress, hs, prependRun]
    | cons q rs =>
      rcases q with ⟨b, n⟩
      intro p hp
      cases he : equal a b with
      | true =>
        have hm : p = (a, n + 1) ∨ p ∈ rs := by simpa [compress, hs, prependRun, he] using hp
        rcases hm with rfl | hm
        · exact Nat.zero_lt_succ n
        · exact ih p (by rw [hs]; exact List.mem_cons_of_mem _ hm)
      | false =>
        have hm : p = (a, 1) ∨ p ∈ (b, n) :: rs := by simpa [compress, hs, prependRun, he] using hp
        rcases hm with rfl | hm
        · exact Nat.zero_lt_succ 0
        · exact ih p (by rw [hs]; exact hm)

private theorem coefficients_prepend_map {α : Type} (equal : α → α → Bool)
    (f : α → Ordinal.{0}) (a : α) (rs : Runs α)
    (heq : ∀ p ∈ rs, equal a p.1 = true → f a = f p.1) :
    (expand (prependRun equal a rs)).map f = f a :: (expand rs).map f := by
  cases rs with
  | nil => rfl
  | cons q rs =>
    rcases q with ⟨b, n⟩
    cases he : equal a b with
    | false => simp [prependRun, he, expand, copies]
    | true =>
      have hv := heq (b, n) List.mem_cons_self he
      simp only [prependRun, he, Bool.cond_true, expand, copies,
        List.map_append, List.map_cons, copies_map, hv, List.cons_append]

theorem compress_expand_values {α : Type} (equal : α → α → Bool)
    (f : α → Ordinal.{0}) (as : List α)
    (heq : ∀ a ∈ as, ∀ b ∈ as, equal a b = true → f a = f b) :
    (expand (compress equal as)).map f = as.map f := by
  revert heq
  induction as with
  | nil => intro _; rfl
  | cons a as ih =>
    intro heq
    rw [compress, coefficients_prepend_map equal f a _
      (fun p hp => heq a List.mem_cons_self p.1
        (List.mem_cons_of_mem _ (compress_head_mem equal as p hp)))]
    rw [ih (fun a ha b hb => heq a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))]
    rfl

private theorem coefficients_prepend_descending {α : Type} (equal : α → α → Bool)
    (f : α → Ordinal.{0}) (a : α) (rs : Runs α)
    (hdesc : rs.Pairwise (fun p q => f q.1 < f p.1))
    (hbound : ∀ p ∈ rs, f p.1 ≤ f a)
    (heq : ∀ p ∈ rs, equal a p.1 = true ↔ f a = f p.1) :
    (prependRun equal a rs).Pairwise (fun p q => f q.1 < f p.1) := by
  cases rs with
  | nil => simp [prependRun]
  | cons q rs =>
    rcases q with ⟨b, n⟩
    have ht := List.pairwise_cons.mp hdesc
    cases he : equal a b with
    | true =>
      have hv := (heq (b, n) List.mem_cons_self).mp he
      simp only [prependRun, he, Bool.cond_true]
      apply List.pairwise_cons.mpr
      exact ⟨fun p hp => by simpa only [hv] using ht.1 p hp, ht.2⟩
    | false =>
      have hba : f b < f a := by
        apply lt_of_le_of_ne (hbound (b, n) List.mem_cons_self)
        intro hv
        have hf := (heq (b, n) List.mem_cons_self).mpr hv.symm
        rw [he] at hf
        cases hf
      simp only [prependRun, he, Bool.cond_false]
      apply List.pairwise_cons.mpr
      refine ⟨?_, hdesc⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hba
      · exact (ht.1 p hp).trans hba

theorem compress_descending {α : Type} (equal : α → α → Bool)
    (f : α → Ordinal.{0}) (as : List α)
    (hordered : as.Pairwise (fun a b => f b ≤ f a))
    (heq : ∀ a ∈ as, ∀ b ∈ as, equal a b = true ↔ f a = f b) :
    (compress equal as).Pairwise (fun p q => f q.1 < f p.1) := by
  revert hordered heq
  induction as with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons a as ih =>
    intro hordered heq
    have ht := List.pairwise_cons.mp hordered
    apply coefficients_prepend_descending equal f a _
      (ih ht.2 (fun a ha b hb => heq a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)))
    · exact fun p hp => ht.1 p.1 (compress_head_mem equal as p hp)
    · exact fun p hp => heq a List.mem_cons_self p.1
        (List.mem_cons_of_mem _ (compress_head_mem equal as p hp))

def coefficientForm (r c : Nat) : Runs (RelativeTerm Nat) :=
  compress (Theta.equal r) (Principal.normalizedAtoms r c)

theorem coefficientForm_primrec : Primrec₂ coefficientForm :=
  ((compress_primrec (.parameter 0) Theta.equal Theta.Effective.equal_primrec).comp
    (Primrec.fst.pair Principal.normalizedAtoms_primrec)).to₂

theorem coefficientForm_positive (r c : Nat) :
    ∀ p ∈ coefficientForm r c, 0 < p.2 := compress_positive _ _

theorem coefficientForm_head_mem (r c : Nat) (p : RelativeTerm Nat × Nat)
    (hp : p ∈ coefficientForm r c) : p.1 ∈ Principal.normalizedAtoms r c :=
  compress_head_mem _ _ p hp

theorem coefficientForm_head_admitted (r c : Nat) (hc : checkCode r c = true)
    (p : RelativeTerm Nat × Nat) (hp : p ∈ coefficientForm r c) :
    checkCode r p.1.code = true ∧ Theta.Normal r p.1 ∧
      0 < denote r p.1 ∧ Ordinal.IsPrincipal (· + ·) (denote r p.1) :=
  Principal.normalizedAtoms_admitted r c hc p.1 (coefficientForm_head_mem r c p hp)

theorem coefficientForm_head_low (r c : Nat) (hc : lowCheckCode r c = true)
    (p : RelativeTerm Nat × Nat) (hp : p ∈ coefficientForm r c) :
    lowCheckCode r p.1.code = true :=
  Principal.normalizedAtoms_low r c hc p.1 (coefficientForm_head_mem r c p hp)

private theorem coefficients_equal_exact (r c : Nat) (hc : checkCode r c = true)
    (a : RelativeTerm Nat) (ha : a ∈ Principal.normalizedAtoms r c)
    (b : RelativeTerm Nat) (hb : b ∈ Principal.normalizedAtoms r c) :
    Theta.equal r a b = true ↔ denote r a = denote r b := by
  have hsa := Principal.normalizedAtoms_admitted r c hc a ha
  have hsb := Principal.normalizedAtoms_admitted r c hc b hb
  apply Theta.equal_correct r a b
  · simpa only [checkCode_code] using hsa.1
  · simpa only [checkCode_code] using hsb.1
  · exact hsa.2.1
  · exact hsb.2.1

theorem coefficientForm_expansion (r c : Nat) (hc : checkCode r c = true) :
    (expand (coefficientForm r c)).map (denote r) = canonicalANF (interpretation r c) := by
  rw [coefficientForm, compress_expand_values _ _ _
    (fun a ha b hb => (coefficients_equal_exact r c hc a ha b hb).mp)]
  exact Principal.normalizedAtoms_anf r c hc

theorem coefficientForm_descending (r c : Nat) (hc : checkCode r c = true) :
    (coefficientForm r c).Pairwise (fun p q => denote r q.1 < denote r p.1) := by
  apply compress_descending _ (denote r) _
  · have hn := (canonicalANF_normal (interpretation r c)).2
    rw [← Principal.normalizedAtoms_anf r c hc] at hn
    simpa only [List.pairwise_map] using hn
  · exact coefficients_equal_exact r c hc

noncomputable def interpretation (r : Nat) (rs : Runs (RelativeTerm Nat)) : Ordinal.{0} :=
  principalSum ((expand rs).map (denote r))

/-- Each natural coefficient is on the right of its actual ordinal head. -/
noncomputable def weightedSum {α : Type} (f : α → Ordinal.{0}) : Runs α → Ordinal.{0}
  | [] => 0
  | (a, n) :: rs => f a * (n : Ordinal.{0}) + weightedSum f rs

theorem expand_weightedSum {α : Type} (f : α → Ordinal.{0}) (rs : Runs α) :
    principalSum ((expand rs).map f) = weightedSum f rs := by
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    rcases p with ⟨a, n⟩
    rw [expand, List.map_append, principalSum_append, copies_map,
      copies_replicate, principalSum_replicate, ih]
    rfl

theorem coefficientForm_value (r c : Nat) (hc : checkCode r c = true) :
    interpretation r (coefficientForm r c) = Hereditary.interpretation r c := by
  rw [interpretation, coefficientForm_expansion r c hc, principalSum_canonicalANF]

theorem coefficientForm_weighted_value (r c : Nat) (hc : checkCode r c = true) :
    weightedSum (denote r) (coefficientForm r c) = Hereditary.interpretation r c :=
  (expand_weightedSum _ _).symm.trans (coefficientForm_value r c hc)

def reconstruct (r : Nat) (rs : Runs (RelativeTerm Nat)) : RelativeTerm Nat :=
  Theta.Normalization.buildAtoms r (expand rs)

theorem reconstruct_primrec : Primrec₂ reconstruct :=
  (Theta.Normalization.Effective.buildAtoms_primrec.comp Primrec.fst
    (expand_primrec.comp Primrec.snd)).to₂

theorem coefficientForm_reconstruct (r c : Nat) (hc : checkCode r c = true) :
    check r (reconstruct r (coefficientForm r c)) = true ∧
      Theta.Normal r (reconstruct r (coefficientForm r c)) ∧
      denote r (reconstruct r (coefficientForm r c)) = Hereditary.interpretation r c := by
  let t := Principal.normalizedTree r c
  let n := SourceOne.PublicCodes.fragment t
  have hs := Principal.normalizedTree_spec r c hc
  have ht : admissible r n t := (finiteCheck_iff r n t).mp hs.1
  have good : Theta.Normalization.GoodAtoms r n (expand (coefficientForm r c)) := by
    intro a ha
    obtain ⟨p, hp, he⟩ := expand_mem _ a ha
    subst a
    exact Theta.Normalization.GoodAtoms.atoms r n t ht hs.2.1 p.1
      (coefficientForm_head_mem r c p hp)
  have hn : IsAdditiveNormalForm ((expand (coefficientForm r c)).map (denote r)) := by
    rw [coefficientForm_expansion r c hc]
    exact canonicalANF_normal _
  exact ⟨Theta.admitted_checked (Theta.Normalization.buildAtoms_admissible r n _ good),
    Theta.Normalization.buildAtoms_normal r n _ good hn,
    (Theta.Normalization.buildAtoms_denote r _).trans (coefficientForm_value r c hc)⟩

theorem coefficientForm_reconstruct_low (r c : Nat) (hc : lowCheckCode r c = true) :
    lowCheck r (reconstruct r (coefficientForm r c)) = true := by
  have hc' := (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using hc)).1
  have hs := coefficientForm_reconstruct r c hc'
  have hb : denote r (reconstruct r (coefficientForm r c)) < finiteBase (r + 1) := by
    rw [hs.2.2]
    exact (lt_nextBase_iff_code r _).mpr ⟨c, hc, rfl⟩
  have hsort := (denote_lt_iff_outerSort_le r _ hs.1 1 (Nat.zero_lt_succ 0)).mp
    (hb.trans (finiteBase_lt_cardinal r))
  simp only [lowCheck, hs.1, hsort, decide_true, Bool.true_and]

/-- Source codes retain each chosen literal head and its positive coefficient. -/
def coefficientCodes (r c : Nat) : Runs Nat :=
  (coefficientForm r c).map (fun p => (p.1.code, p.2))

theorem coefficientCodes_primrec : Primrec₂ coefficientCodes := by
  have hh : Primrec₂ (fun (_ : Nat × Nat) (p : RelativeTerm Nat × Nat) => (p.1.code, p.2)) :=
    ((code_primrec.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_map coefficientForm_primrec hh).to₂

theorem coefficientCodes_positive (r c : Nat) :
    ∀ p ∈ coefficientCodes r c, 0 < p.2 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact coefficientForm_positive r c q hq

theorem coefficientCodes_head_admitted (r c : Nat) (hc : checkCode r c = true)
    (p : Nat × Nat) (hp : p ∈ coefficientCodes r c) :
    checkCode r p.1 = true ∧ Theta.Normal r (ThetaCourse.rawTree p.1) ∧
      0 < Hereditary.interpretation r p.1 ∧
      Ordinal.IsPrincipal (· + ·) (Hereditary.interpretation r p.1) := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  simpa only [ThetaCourse.rawTree_code, interpretation_code] using
    coefficientForm_head_admitted r c hc q hq

theorem coefficientCodes_head_low (r c : Nat) (hc : lowCheckCode r c = true)
    (p : Nat × Nat) (hp : p ∈ coefficientCodes r c) : lowCheckCode r p.1 = true := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact coefficientForm_head_low r c hc q hq

theorem coefficientCodes_descending (r c : Nat) (hc : checkCode r c = true) :
    (coefficientCodes r c).Pairwise
      (fun p q => Hereditary.interpretation r q.1 < Hereditary.interpretation r p.1) := by
  simpa only [coefficientCodes, List.pairwise_map, interpretation_code] using
    coefficientForm_descending r c hc

theorem expand_map {α β : Type} (f : α → β) (rs : Runs α) :
    expand (rs.map (fun p => (f p.1, p.2))) = (expand rs).map f := by
  induction rs with
  | nil => rfl
  | cons p rs ih => cases p; simp only [List.map_cons, expand, copies_map, List.map_append, ih]

theorem coefficientCodes_expansion (r c : Nat) (hc : checkCode r c = true) :
    (expand (coefficientCodes r c)).map (Hereditary.interpretation r) =
      canonicalANF (Hereditary.interpretation r c) := by
  simpa only [coefficientCodes, expand_map, List.map_map, Function.comp_def, interpretation_code] using
    coefficientForm_expansion r c hc

theorem coefficientCodes_weighted_value (r c : Nat) (hc : checkCode r c = true) :
    weightedSum (Hereditary.interpretation r) (coefficientCodes r c) =
      Hereditary.interpretation r c := by
  rw [← expand_weightedSum, coefficientCodes_expansion r c hc, principalSum_canonicalANF]

def expandedCodes (r c : Nat) : List Nat := expand (coefficientCodes r c)

theorem expandedCodes_primrec : Primrec₂ expandedCodes :=
  (expand_primrec.comp coefficientCodes_primrec).to₂

def reconstructCode (r c : Nat) : Nat := (reconstruct r (coefficientForm r c)).code

theorem reconstructCode_primrec : Primrec₂ reconstructCode :=
  (code_primrec.comp (reconstruct_primrec.comp Primrec.fst coefficientForm_primrec)).to₂

theorem reconstructCode_checked (r c : Nat) (hc : checkCode r c = true) :
    checkCode r (reconstructCode r c) = true ∧
      Theta.Normal r (ThetaCourse.rawTree (reconstructCode r c)) ∧
      Hereditary.interpretation r (reconstructCode r c) = Hereditary.interpretation r c := by
  simpa only [reconstructCode, checkCode_code, ThetaCourse.rawTree_code, interpretation_code] using
    coefficientForm_reconstruct r c hc

theorem reconstructCode_low (r c : Nat) (hc : lowCheckCode r c = true) :
    lowCheckCode r (reconstructCode r c) = true := by
  simpa only [reconstructCode, lowCheckCode_code] using coefficientForm_reconstruct_low r c hc

theorem coefficientForm_computable : Computable₂ coefficientForm := coefficientForm_primrec.to_comp

theorem coefficientCodes_computable : Computable₂ coefficientCodes := coefficientCodes_primrec.to_comp

end Alexander313.Wilken.RelativeTerm.Hereditary.Coefficients
