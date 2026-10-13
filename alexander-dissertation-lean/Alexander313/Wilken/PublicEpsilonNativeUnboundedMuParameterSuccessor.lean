import Alexander313.Wilken.HereditaryParameterSuccessorBounds
import Alexander313.Wilken.PublicEpsilonNativeUnboundedMu
import Alexander313.Wilken.HereditaryNativeUniformPublicReturn
import Alexander313.Wilken.PublicEpsilonSourceDictionarySupport
import Alexander313.Wilken.HereditaryOmegaPowers
import Alexander313.Wilken.HereditaryNativeMuSuccessorIntervals

/-!
# Concrete lower-context successors for below-base mu values

Actual mu execution supplies its canonical SAME-value public code. For a
non-epsilon mu, the genuine bounded endpoint scan and actual original-source
return construct a checked Normal theta-zero representative at a lower
finite source context. Its normalized argument-plus-one operation is checked
and remains below the original root. For an epsilon mu, the returned public
code is genuinely an admitted self-context and its real theta_mu(0) and
theta_mu(1) presentations give the same bound.

The contexts are recorded explicitly. Neither numerical public canonicality
nor these bounds identifies the successor convention of an arbitrary
parameter in the active root context. That printed provenance obligation
remains separate; no new parameter-plus operation is defined. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.MuParameterSuccessor

open ThetaCourse

def sourceSuccessorTerm (r : Nat) (b : RelativeTerm Nat) : RelativeTerm Nat :=
  .theta 0 (Theta.Normalization.normalize r (.sum b (rawTree (OmegaPowers.numeralAt r 1))))

theorem sourceSuccessorTerm_primrec : Primrec₂ sourceSuccessorTerm := by
  have hu := rawTree_primrec.comp (OmegaPowers.numeralAt_primrec.comp Primrec.fst (Primrec.const 1))
  have ht := sum_primrec.comp Primrec.snd hu
  exact (theta_primrec.comp (Primrec.const 0)
    (Theta.Normalization.Effective.normalize_primrec.comp Primrec.fst ht)).to₂

/-- Genuine original hereditary admission, including source level zero,
constructs the literal argument-plus-one operation at the SAME context. -/
theorem sourceSuccessorTerm_spec (r : Nat) (b : RelativeTerm Nat)
    (ht : check r (.theta 0 b) = true) :
    check r (sourceSuccessorTerm r b) = true ∧
      Theta.Normal r (sourceSuccessorTerm r b) ∧
      (sourceSuccessorTerm r b).outerSort ≤ 1 ∧
      denote r (sourceSuccessorTerm r b) = globalCollapse (finiteBase r) 0 (denote r b + 1) := by
  have hb := SourceFixedPoint.checked_theta_argument r 0 b ht
  let unit := rawTree (OmegaPowers.numeralAt r 1)
  have hulow : lowCheck r unit = true := by
    obtain ⟨u, he, hu⟩ := (lowCheckCode_iff r _).mp (OmegaPowers.numeralAt_checked r 1)
    simpa only [unit, ← he, rawTree_code] using hu
  have hu : check r unit = true := (Bool.and_eq_true.mp hulow).1
  have hunitcode : unit.code = OmegaPowers.numeralAt r 1 := by
    obtain ⟨u, he, _⟩ := (lowCheckCode_iff r _).mp (OmegaPowers.numeralAt_checked r 1)
    simpa only [unit, ← he, rawTree_code] using he
  have huv : denote r unit = 1 := by
    rw [← interpretation_code r unit, hunitcode, OmegaPowers.numeralAt_value, Nat.cast_one]
  have hs : check r (.sum b unit) = true := by
    rw [Uniform.check_sum, hb, hu]
    rfl
  let n := SourceOne.PublicCodes.fragment (.sum b unit)
  have had := Theta.checked_admissible r n (.sum b unit) hs
    (SourceOne.PublicCodes.height_le_fragment _)
  let t := Theta.Normalization.normalize r (.sum b unit)
  have hc : check r t = true := Theta.Normalization.normalize_checked r n _ had
  have hn : Theta.Normal r t := Theta.Normalization.normalize_normal r n _ had
  have hv : denote r t = denote r b + 1 := by
    rw [Theta.Normalization.normalize_denote r n _ had]
    change denote r b + denote r unit = _
    rw [huv]
  have hsort : t.outerSort ≤ 2 :=
    (denote_lt_iff_outerSort_le r t hc 2 (by omega)).mp (by
      rw [hv]
      exact (omegaSequence_isSuccLimit (finiteBase r) 1).add_one_lt
        (SourceFixedPoint.checked_theta_sort r 0 b ht))
  refine ⟨?_, ?_, by simp only [sourceSuccessorTerm, RelativeTerm.outerSort], ?_⟩
  · change check r (.theta 0 t) = true
    rw [Uniform.check_theta, hc]
    simp only [Nat.zero_add, hsort, decide_true, Bool.true_and]
  · exact (Theta.normal_theta r 0 t).mpr hn
  · change globalCollapse (finiteBase r) 0 (denote r t) = _
    rw [hv]

/-- The existing numerical scan genuinely chooses a source level below
the principal value; its stored public level is not assumed least. -/
theorem principal_level_lower (p : Nat) (hp : Canonical.check p = true)
    (hpos : 0 < unionInterpretation p) :
    finiteBase (PublicEpsilonSourceDictionary.level p) ≤ unionInterpretation p := by
  cases hm : PublicEpsilonSourceDictionary.level p with
  | zero =>
    rw [hm, finiteBase_zero]
    exact Order.one_le_iff_pos.mpr hpos
  | succ m =>
    have hlt : m < PublicEpsilonSourceDictionary.level p := by
      rw [hm]
      exact Nat.lt_succ_self m
    simpa only [hm] using (PublicEpsilonSourceDictionary.level_bound p hp).2.2 m hlt

/-- The real source return and its actual complete ANF produce the lower
theta presentation for every positive additive-principal public value. -/
theorem principal_sourceTerm_spec (p : Nat) (hp : Canonical.check p = true)
    (hpos : 0 < unionInterpretation p)
    (hprincipal : Ordinal.IsPrincipal (· + ·) (unionInterpretation p)) :
    ∃ b : RelativeTerm Nat, PublicEpsilonSourceDictionary.sourceTerm p = .theta 0 b ∧
      check (PublicEpsilonSourceDictionary.level p) (.theta 0 b) = true ∧
      Theta.Normal (PublicEpsilonSourceDictionary.level p) (.theta 0 b) ∧
      denote (PublicEpsilonSourceDictionary.level p) (.theta 0 b) = unionInterpretation p := by
  have hs := SourceZeta.Transport.returnCode_spec (PublicEpsilonSourceDictionary.level p) p hp
    (PublicEpsilonSourceDictionary.level_bound p hp).2.1
  have hl := (Theta.acceptedLowCode_iff _ _).mp hs.1
  have hc : checkCode (PublicEpsilonSourceDictionary.level p)
      (PublicEpsilonSourceDictionary.sourceCode p) = true :=
    (Bool.and_eq_true.mp (by simpa only [lowCheckCode_eq] using hl.1)).1
  have hi := (SourceDecomposition.inputCheck_exact _ _).mpr ⟨hc, hl.2⟩
  have hw := SourceDecomposition.word_spec _ _ hi
  have hmap : (SourceDecomposition.word (PublicEpsilonSourceDictionary.level p)
      (PublicEpsilonSourceDictionary.sourceCode p)).map
      (denote (PublicEpsilonSourceDictionary.level p)) = [unionInterpretation p] := by
    rw [hw.2, hs.2, canonicalANF_principal hpos hprincipal]
  have hlength : (SourceDecomposition.word (PublicEpsilonSourceDictionary.level p)
      (PublicEpsilonSourceDictionary.sourceCode p)).length = 1 := by
    simpa only [List.length_map, List.length_singleton] using congrArg List.length hmap
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.mp hlength
  have htmem : t ∈ SourceDecomposition.word (PublicEpsilonSourceDictionary.level p)
      (PublicEpsilonSourceDictionary.sourceCode p) := by
    rw [ht]
    exact List.mem_singleton_self _
  have hts := hw.1 t htmem
  have htv : denote (PublicEpsilonSourceDictionary.level p) t = unionInterpretation p := by
    simpa only [ht, List.map_singleton, List.singleton_inj] using hmap
  have hout : t.outerSort ≤ 1 :=
    (denote_lt_iff_outerSort_le _ t hts.1 1 (by omega)).mp (by
      rw [htv]
      exact (PublicEpsilonSourceDictionary.level_bound p hp).2.1.trans
        (finiteBase_lt_cardinal (PublicEpsilonSourceDictionary.level p)))
  rcases SourceDecomposition.word_shape _ _ t htmem with ⟨u, rfl⟩ | ⟨k, b, rfl⟩
  · have had := Theta.checked_admissible _ (SourceOne.PublicCodes.fragment (.parameter u))
      (.parameter u) hts.1 (SourceOne.PublicCodes.height_le_fragment _)
    have hsmall := parameter_sound _ u had.1
    exact False.elim ((hsmall.trans_le (principal_level_lower p hp hpos)).ne htv)
  · have hk : k = 0 := by simp only [RelativeTerm.outerSort] at hout; omega
    subst k
    refine ⟨b, ?_, hts.1, hts.2.1, htv⟩
    simp only [PublicEpsilonSourceDictionary.sourceTerm, ht, List.head?_cons, Option.getD_some]

end Alexander313.Wilken.RelativeTerm.Hereditary.MuParameterSuccessor

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.ParameterSuccessor

def publicMu (q root : Nat) : Nat := UniformPublicReturn.publicCode (betaCode q root) (muCode q root)

theorem publicMu_primrec : Primrec (fun p : Context => publicMu p.1 p.2) :=
  UniformPublicReturn.publicCode_primrec.comp betaCode_primrec muCode_primrec

theorem publicMu_spec (q root : Nat) (ha : Mu.inputCheck q root = true) :
    Canonical.check (publicMu q root) = true ∧ unionInterpretation (publicMu q root) = sourceValue q root := by
  have hm := muCode_spec q root ha
  have hs := UniformPublicReturn.publicCode_spec (betaCode q root) (muCode q root)
    ((UniformPublicReturn.inputCheck_exact _ _).mpr hm.1)
  exact ⟨hs.1, hs.2.trans hm.2.2⟩

theorem publicMu_positive (q root : Nat) (ha : Mu.inputCheck q root = true) :
    0 < unionInterpretation (publicMu q root) := by
  rw [(publicMu_spec q root ha).2, sourceValue]
  exact Ordinal.opow_pos _ Ordinal.omega0_pos

theorem publicMu_principal (q root : Nat) (ha : Mu.inputCheck q root = true) :
    Ordinal.IsPrincipal (· + ·) (unionInterpretation (publicMu q root)) := by
  rw [(publicMu_spec q root ha).2, sourceValue]
  exact Ordinal.isPrincipal_add_omega0_opow _

def lowerSuccessorTerm (q root : Nat) : RelativeTerm Nat :=
  MuParameterSuccessor.sourceSuccessorTerm (PublicEpsilonSourceDictionary.level (publicMu q root))
    (ThetaCourse.rawTree (Localization.argumentCode (PublicEpsilonSourceDictionary.sourceTerm
      (publicMu q root)).code))

theorem lowerSuccessorTerm_primrec : Primrec
    (fun p : Context => lowerSuccessorTerm p.1 p.2) :=
  MuParameterSuccessor.sourceSuccessorTerm_primrec.comp
    (PublicEpsilonSourceDictionary.level_primrec.comp publicMu_primrec)
    (ThetaCourse.rawTree_primrec.comp (Localization.argumentCode_primrec.comp
      (code_primrec.comp (PublicEpsilonSourceDictionary.sourceTerm_primrec.comp publicMu_primrec))))

/-- Original execution and the non-epsilon below-root branch derive the
concrete lower-source representative, its LOW argument and its checked
literal successor. The source level is an output, not a chosen context oracle. -/
theorem non_epsilon_lower_successor (q root : Nat) (ha : Mu.inputCheck q root = true)
    (hne : Ordinal.omega0 ^ sourceValue q root ≠ sourceValue q root)
    (hsmall : sourceValue q root < interpretation q root) :
    Hereditary.check (PublicEpsilonSourceDictionary.level (publicMu q root)) (lowerSuccessorTerm q root) = true ∧
      Theta.Normal (PublicEpsilonSourceDictionary.level (publicMu q root)) (lowerSuccessorTerm q root) ∧
      sourceValue q root < Hereditary.denote (PublicEpsilonSourceDictionary.level (publicMu q root))
        (lowerSuccessorTerm q root) ∧
      Hereditary.denote (PublicEpsilonSourceDictionary.level (publicMu q root)) (lowerSuccessorTerm q root) <
        interpretation q root := by
  let p := publicMu q root
  let r := PublicEpsilonSourceDictionary.level p
  have hp := publicMu_spec q root ha
  obtain ⟨b, hb, hc, hn, hv⟩ := MuParameterSuccessor.principal_sourceTerm_spec p hp.1
    (publicMu_positive q root ha) (publicMu_principal q root ha)
  have hcode : lowerSuccessorTerm q root = MuParameterSuccessor.sourceSuccessorTerm r b := by
    change MuParameterSuccessor.sourceSuccessorTerm r
      (ThetaCourse.rawTree (Localization.argumentCode (PublicEpsilonSourceDictionary.sourceTerm p).code)) = _
    rw [hb, Localization.argumentCode_theta, ThetaCourse.rawTree_code]
  have hs := MuParameterSuccessor.sourceSuccessorTerm_spec r b hc
  have hbc := SourceFixedPoint.checked_theta_argument r 0 b hc
  have he : globalCollapse (finiteBase r) 0 (Hereditary.denote r b) = sourceValue q root :=
    hv.trans hp.2
  have hnext := ParameterSuccessorBounds.non_epsilon_successor_interval (finiteBase r)
    (finiteBase_epsilon_or_one r) (SourceFixedPoint.sourceOrdinal r 0 b hbc)
    (SourceFixedPoint.checked_theta_sort r 0 b hc) (by rw [he]; exact hne)
    (interpretation q root) (root_epsilon q root ha) (he.trans_lt hsmall)
  rw [hcode]
  exact ⟨hs.1, hs.2.1, by rw [hs.2.2.2]; exact he.symm.trans_lt hnext.1,
    by rw [hs.2.2.2]; exact hnext.2⟩

def selfSuccessorTerm (q root : Nat) : RelativeTerm Nat :=
  NativeContext.Mu.SuccessorIntervals.sourceSuccessorTerm (publicMu q root) Normalization.zeroTree

theorem selfSuccessorTerm_primrec : Primrec
    (fun p : Context => selfSuccessorTerm p.1 p.2) :=
  NativeContext.Mu.SuccessorIntervals.sourceSuccessorTerm_primrec.comp publicMu_primrec
    (Primrec.const Normalization.zeroTree)

/-- A genuinely epsilon mu yields its actual canonical self-context,
including checked theta_mu(0)=mu and the literal argument-one successor.
This follows the self-context presentation of a parameter in printed 3.40;
its identification with the parameter-plus convention is not asserted. -/
theorem epsilon_self_successor (q root : Nat) (ha : Mu.inputCheck q root = true)
    (he : Ordinal.omega0 ^ sourceValue q root = sourceValue q root)
    (hsmall : sourceValue q root < interpretation q root) :
    baseCheck (publicMu q root) = true ∧
      check (publicMu q root) SourceChi.Powers.baseTree = true ∧
      denote (publicMu q root) SourceChi.Powers.baseTree = sourceValue q root ∧
      check (publicMu q root) (selfSuccessorTerm q root) = true ∧
      Comparison.Normal (publicMu q root) (selfSuccessorTerm q root) ∧
      sourceValue q root < denote (publicMu q root) (selfSuccessorTerm q root) ∧
      denote (publicMu q root) (selfSuccessorTerm q root) < interpretation q root := by
  have hp := publicMu_spec q root ha
  have hbase : baseCheck (publicMu q root) = true :=
    (baseCheck_exact _).mpr ⟨Canonical.check_original hp.1, by change
      Ordinal.omega0 ^ unionInterpretation (publicMu q root) = unionInterpretation (publicMu q root)
      rw [hp.2]; exact he⟩
  have hb := SourceChi.Powers.baseTree_checked (publicMu q root) hbase
  have hbv : denote (publicMu q root) SourceChi.Powers.baseTree = sourceValue q root :=
    (SourceChi.Powers.baseTree_value _ hbase).trans hp.2
  have hs := NativeContext.Mu.SuccessorIntervals.sourceSuccessorTerm_spec (publicMu q root)
    Normalization.zeroTree hb
  have hv : denote (publicMu q root) (selfSuccessorTerm q root) =
      globalCollapse (sourceValue q root) 0 1 := by
    rw [selfSuccessorTerm, hs.2.2.2, Normalization.zeroTree_denote, zero_add]
    change globalCollapse (unionInterpretation (publicMu q root)) 0 1 = _
    rw [hp.2]
  have hi := ParameterSuccessorBounds.epsilon_self_successor_interval (sourceValue q root)
    (interpretation q root) he (root_epsilon q root ha) hsmall
  exact ⟨hbase, hb, hbv, hs.1, hs.2.1, by rw [hv]; exact hi.2.1,
    by rw [hv]; exact hi.2.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.Mu.ParameterSuccessor
