import Alexander313.Wilken.HereditaryThetaNormalizationPrimitive

/-! # Actual principal decomposition and additive-principal recognition

Normalize an arbitrary originally admitted source tree, then open its actual
earlier-level payload atoms. Their values are the genuine canonical additive
normal form. Its length is one exactly for a positive additive principal;
the empty list is exactly zero. Every returned low atom retains the original
low admission. Recognition and decomposition are uniformly primitive recursive.
This does not classify epsilon or multiplicative principal numbers, implement
logarithms/powers, or assert uniqueness of source-tree spellings. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.Principal

open Theta ThetaCourse

private theorem principal_list_length_one (xs : List Ordinal.{0})
    (hx : xs.length = 1) : ∃ a, xs = [a] := by
  cases xs with
  | nil => simp at hx
  | cons a as =>
    cases as with
    | nil => exact ⟨a, rfl⟩
    | cons b bs => simp at hx

theorem canonicalANF_length_one_iff (ξ : Ordinal.{0}) :
    (canonicalANF ξ).length = 1 ↔ 0 < ξ ∧ Ordinal.IsPrincipal (· + ·) ξ := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := principal_list_length_one (canonicalANF ξ) h
    have hv : a = ξ := by
      simpa only [ha, principalSum, add_zero] using principalSum_canonicalANF ξ
    have hm : ξ ∈ canonicalANF ξ := by rw [ha, hv]; simp
    exact (canonicalANF_normal ξ).1 ξ hm
  · rintro ⟨hp, hprincipal⟩
    simpa only [canonicalANF_principal hp hprincipal, List.length_singleton]

def normalizedTree (r c : Nat) : RelativeTerm Nat :=
  rawTree (Normalization.normalizeCode r c)

theorem normalizedTree_primrec : Primrec₂ normalizedTree :=
  (rawTree_primrec.comp Normalization.Effective.normalizeCode_primrec).to₂

theorem normalizedTree_spec (r c : Nat) (hc : checkCode r c = true) :
    check r (normalizedTree r c) = true ∧ Normal r (normalizedTree r c) ∧
      denote r (normalizedTree r c) = interpretation r c := by
  have hs := Normalization.normalizeCode_checked r c hc
  obtain ⟨t, ht, htcheck⟩ := (checkCode_iff r _).mp hs.1
  refine ⟨?_, hs.2.1, ?_⟩
  · simpa only [normalizedTree, ← ht, rawTree_code] using htcheck
  · simpa only [normalizedTree, ← ht, rawTree_code, interpretation_code] using hs.2.2

def normalizedAtoms (r c : Nat) : List (RelativeTerm Nat) := atoms r (normalizedTree r c)

theorem normalizedAtoms_primrec : Primrec₂ normalizedAtoms :=
  (Theta.Effective.atoms_primrec.comp Primrec.fst normalizedTree_primrec).to₂

theorem normalizedAtoms_anf (r c : Nat) (hc : checkCode r c = true) :
    (normalizedAtoms r c).map (denote r) = canonicalANF (interpretation r c) := by
  have hs := normalizedTree_spec r c hc
  let t := normalizedTree r c
  have ha := (finiteCheck_iff r (SourceOne.PublicCodes.fragment t) t).mp hs.1
  have h := atoms_denote_anf r (SourceOne.PublicCodes.fragment t) t ha hs.2.1
  simpa only [normalizedAtoms, t, hs.2.2] using h

theorem normalizedAtoms_admitted (r c : Nat) (hc : checkCode r c = true)
    (a : RelativeTerm Nat) (ha : a ∈ normalizedAtoms r c) :
    checkCode r a.code = true ∧ Normal r a ∧
      0 < denote r a ∧ Ordinal.IsPrincipal (· + ·) (denote r a) := by
  have hs := normalizedTree_spec r c hc
  let t := normalizedTree r c
  have ht := (finiteCheck_iff r (SourceOne.PublicCodes.fragment t) t).mp hs.1
  have haa := atoms_admissible r (SourceOne.PublicCodes.fragment t) t a ht hs.2.1 ha
  have hna := atoms_normal r (SourceOne.PublicCodes.fragment t) t a ht hs.2.1 ha
  have hmem : denote r a ∈ canonicalANF (interpretation r c) := by
    rw [← normalizedAtoms_anf r c hc]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  exact ⟨by simpa only [checkCode_code] using admitted_checked haa, hna,
    (canonicalANF_normal _).1 _ hmem⟩

theorem normalizedAtoms_low (r c : Nat) (hc : lowCheckCode r c = true)
    (a : RelativeTerm Nat) (ha : a ∈ normalizedAtoms r c) : lowCheckCode r a.code = true := by
  have hc' : checkCode r c = true :=
    (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using hc)).1
  have hs := normalizedTree_spec r c hc'
  let t := normalizedTree r c
  have ht := (finiteCheck_iff r (SourceOne.PublicCodes.fragment t) t).mp hs.1
  have hvalue : denote r t < finiteBase (r + 1) := by
    rw [hs.2.2]
    exact (lt_nextBase_iff_code r _).mpr ⟨c, hc, rfl⟩
  simpa only [lowCheckCode_code] using
    atoms_low r (SourceOne.PublicCodes.fragment t) t a ht hs.2.1 ha hvalue

theorem normalizedAtoms_length (r c : Nat) (hc : checkCode r c = true) :
    (normalizedAtoms r c).length = (canonicalANF (interpretation r c)).length := by
  simpa only [List.length_map] using congrArg List.length (normalizedAtoms_anf r c hc)

theorem normalizedAtoms_zero_iff (r c : Nat) (hc : checkCode r c = true) :
    normalizedAtoms r c = [] ↔ interpretation r c = 0 := by
  constructor
  · intro h
    have hv := principalSum_canonicalANF (interpretation r c)
    rw [← normalizedAtoms_anf r c hc, h] at hv
    simpa only [List.map_nil, principalSum] using hv.symm
  · intro h
    apply List.length_eq_zero_iff.mp
    simpa only [normalizedAtoms_length r c hc, h, canonicalANF_zero, List.length_nil]

def atomCodes (r c : Nat) : List Nat := (normalizedAtoms r c).map RelativeTerm.code

theorem atomCodes_primrec : Primrec₂ atomCodes := by
  have hcode : Primrec₂ (fun (_ : Nat × Nat) (a : RelativeTerm Nat) => a.code) :=
    (code_primrec.comp Primrec.snd).to₂
  exact (Primrec.list_map normalizedAtoms_primrec hcode).to₂

theorem atomCodes_anf (r c : Nat) (hc : checkCode r c = true) :
    (atomCodes r c).map (interpretation r) = canonicalANF (interpretation r c) := by
  simpa only [atomCodes, List.map_map, Function.comp_def, interpretation_code] using normalizedAtoms_anf r c hc

def principalCheck (r c : Nat) : Bool :=
  checkCode r c && decide ((normalizedAtoms r c).length = 1)

theorem principalCheck_primrec : Primrec₂ principalCheck :=
  (Primrec.and.comp Uniform.hereditaryCheckCode_primrec
    (Primrec.eq.comp (Primrec.list_length.comp normalizedAtoms_primrec) (Primrec.const 1)).decide).to₂

theorem principalCheck_exact (r c : Nat) : principalCheck r c = true ↔
    checkCode r c = true ∧ 0 < interpretation r c ∧
      Ordinal.IsPrincipal (· + ·) (interpretation r c) := by
  simp only [principalCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hlength⟩
    exact ⟨hc, (canonicalANF_length_one_iff _).mp
      (by rw [← normalizedAtoms_length r c hc]; exact hlength)⟩
  · rintro ⟨hc, hpos, hprincipal⟩
    refine ⟨hc, ?_⟩
    rw [normalizedAtoms_length r c hc]
    exact (canonicalANF_length_one_iff _).mpr ⟨hpos, hprincipal⟩

def principalLowCheck (r c : Nat) : Bool := lowCheckCode r c && principalCheck r c

theorem principalLowCheck_primrec : Primrec₂ principalLowCheck :=
  (Primrec.and.comp Uniform.hereditaryLowCheckCode_primrec principalCheck_primrec).to₂

theorem principalLowCheck_exact (r c : Nat) : principalLowCheck r c = true ↔
    lowCheckCode r c = true ∧ 0 < interpretation r c ∧
      Ordinal.IsPrincipal (· + ·) (interpretation r c) := by
  rw [principalLowCheck, Bool.and_eq_true, principalCheck_exact]
  constructor
  · rintro ⟨hc, _, hp, hprincipal⟩; exact ⟨hc, hp, hprincipal⟩
  · rintro ⟨hc, hp, hprincipal⟩
    exact ⟨hc, (Bool.and_eq_true_iff.mp (by simpa only [lowCheckCode_eq] using hc)).1,
      hp, hprincipal⟩

def unionPrincipalCheck (q : Nat) : Bool := principalLowCheck q.unpair.1 q.unpair.2

theorem unionPrincipalCheck_primrec : Primrec unionPrincipalCheck :=
  principalLowCheck_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)

theorem unionPrincipalCheck_exact (q : Nat) : unionPrincipalCheck q = true ↔
    unionCheck q = true ∧ 0 < unionInterpretation q ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation q) :=
  principalLowCheck_exact q.unpair.1 q.unpair.2

theorem unionPrincipalCheck_computable : Computable unionPrincipalCheck :=
  unionPrincipalCheck_primrec.to_comp

end Alexander313.Wilken.RelativeTerm.Hereditary.Principal
