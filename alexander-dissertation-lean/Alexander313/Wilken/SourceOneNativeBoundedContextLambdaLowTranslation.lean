import Alexander313.Wilken.SourceOneNativeZetaLowValue
import Alexander313.Wilken.SourceOneNativeBoundedPublicReturnCodes

/-!
# Genuine non-epsilon lambda transport over the original source-one outer root

The actual original source-zero return has a complete principal word of
length one at the intermediate root value. Its concrete first-atom parser
therefore supplies an ORIGINAL proper theta-zero lambda caller. Original
admission excludes parameter atoms, and the true LOW range excludes
positive indices. Source-one fixedness retains its one-boundary clause;
the proved logarithm formula then gives actual non-epsilon zeta and lambda
agreement. No Native base-one parser or source-root oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextLambda.LowTranslation

def returnedAtom (a c : Nat) : RelativeTerm Nat :=
  (SourceDecomposition.word 0 (BoundedPublicReturn.sourceTermCode a (ThetaCourse.rawTree c))).head?.getD
    (Theta.Normalization.zeroTree 0)

theorem returnedAtom_primrec : Primrec₂ returnedAtom :=
  (Primrec.option_getD.comp
    (Primrec.list_head?.comp (SourceDecomposition.word_primrec.comp (Primrec.const 0)
      (BoundedPublicReturn.sourceTermCode_primrec.comp Primrec.fst
        (ThetaCourse.rawTree_primrec.comp Primrec.snd))))
    (Primrec.const (Theta.Normalization.zeroTree 0))).to₂

def returnedCode (a c : Nat) : Nat := (returnedAtom a c).code

theorem returnedCode_primrec : Primrec₂ returnedCode := (code_primrec.comp returnedAtom_primrec).to₂

/-- The concrete complete-word parser derives the whole original proper
source-one lambda caller from the original intermediate caller. -/
theorem returnedCode_spec (a c : Nat) (ha : SourceOneIota.rootCheck a = true)
    (hc : NativeContext.DirectZeta.inputCheck (alphaCode a) c = true)
    (hp : NativeContext.base (alphaCode a) < NativeContext.interpretation (alphaCode a) c)
    (hb : NativeContext.interpretation (alphaCode a) c < Enclosure.sourceAlphaPlus a) :
    Lambda.PublicBranches.inputCheck (returnedCode a c) = true ∧
      interpretation 0 (returnedCode a c) = NativeContext.interpretation (alphaCode a) c := by
  obtain ⟨t, rfl, ht, hn⟩ := (NativeContext.DirectZeta.inputCheck_exact _ c).mp hc
  let b := BoundedPublicReturn.sourceTermCode a (.theta 0 t)
  have hs := BoundedPublicReturn.sourceTermCode_low_spec a ha (.theta 0 t) ht hn
    (by simp only [RelativeTerm.outerSort]) (by simpa only [NativeContext.interpretation_code] using hb)
  have hl := (Theta.acceptedLowCode_iff 0 _).mp hs.1
  have hcheck : checkCode 0 b = true :=
    (Bool.and_eq_true.mp (by simpa only [lowCheckCode_eq] using hl.1)).1
  have hi : SourceDecomposition.inputCheck 0 b = true :=
    (SourceDecomposition.inputCheck_exact 0 b).mpr ⟨hcheck, hl.2⟩
  have hw := SourceDecomposition.word_spec 0 b hi
  have hprincipal := NativeContext.SourceChi.Powers.theta_principal (alphaCode a) t ht
  have hv : interpretation 0 b = NativeContext.denote (alphaCode a) (.theta 0 t) := hs.2
  have hmap : (SourceDecomposition.word 0 b).map (denote 0) =
      [NativeContext.denote (alphaCode a) (.theta 0 t)] := by
    rw [hw.2, hv, canonicalANF_principal hprincipal.1 hprincipal.2]
  have hlength : (SourceDecomposition.word 0 b).length = 1 := by
    simpa only [List.length_map, List.length_singleton] using congrArg List.length hmap
  obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp hlength
  have hum : u ∈ SourceDecomposition.word 0 b := by rw [hu]; exact List.mem_singleton_self _
  have hus := hw.1 u hum
  have huv : denote 0 u = NativeContext.denote (alphaCode a) (.theta 0 t) := by
    simpa only [hu, List.map_singleton, List.singleton_inj] using hmap
  have hproper : 1 < NativeContext.denote (alphaCode a) (.theta 0 t) :=
    (EpsilonOffsets.epsilon_one_lt (root_epsilon a ha)).trans (by
      simpa only [alpha_base a ha, NativeContext.interpretation_code] using hp)
  have hout : u.outerSort ≤ 1 := (denote_lt_iff_outerSort_le 0 u hus.1 1 (by omega)).mp (by
    rw [huv, finiteBase_zero, HeightSupport.root_omegaSequence_succ a 0 ha]
    exact (NativeContext.denote_lt_iff_outerSort_le _ _ ht 1 (by omega)).mpr (by
      simp only [RelativeTerm.outerSort]))
  have hatom : returnedAtom a (.theta 0 t : RelativeTerm Nat).code = u := by
    simp only [returnedAtom, ThetaCourse.rawTree_code, hu, List.head?_cons, Option.getD_some]
  rcases SourceDecomposition.word_shape 0 b u hum with ⟨p, rfl⟩ | ⟨k, v, rfl⟩
  · have had := Theta.checked_admissible 0 (SourceOne.PublicCodes.fragment (.parameter p))
      (.parameter p) hus.1 (SourceOne.PublicCodes.height_le_fragment _)
    have hsmall : denote 0 (.parameter p) < finiteBase 0 := parameter_sound _ p had.1
    rw [huv, finiteBase_zero] at hsmall
    exact False.elim (hproper.not_ge hsmall.le)
  · have hk : k = 0 := by simp only [RelativeTerm.outerSort] at hout; omega
    subst k
    have hcode : returnedCode a (.theta 0 t : RelativeTerm Nat).code = (.theta 0 v : RelativeTerm Nat).code :=
      congrArg RelativeTerm.code hatom
    have hguard := (Lambda.PublicBranches.inputCheck_exact _).mpr
      ⟨v, hcode, hus.1, hus.2.1, by rw [huv]; exact hproper⟩
    exact ⟨hguard, by rw [hcode, interpretation_code, huv]; rfl⟩

theorem zeta_value (a c : Nat) (ha : SourceOneIota.rootCheck a = true)
    (hc : NativeContext.DirectZeta.inputCheck (alphaCode a) c = true)
    (hp : NativeContext.base (alphaCode a) < NativeContext.interpretation (alphaCode a) c)
    (hb : NativeContext.interpretation (alphaCode a) c < Enclosure.sourceAlphaPlus a)
    (hε : Ordinal.omega0 ^ NativeContext.interpretation (alphaCode a) c ≠ NativeContext.interpretation (alphaCode a) c) :
    SourceZeta.sourceValue 0 (returnedCode a c) = NativeContext.DirectZeta.sourceValue (alphaCode a) c := by
  have hs := returnedCode_spec a c ha hc hp hb
  have he : Ordinal.omega0 ^ interpretation 0 (returnedCode a c) ≠ interpretation 0 (returnedCode a c) := by
    simpa only [hs.2] using hε
  rw [ZetaLowValue.sourceValue_non_epsilon _ hs.1 he,
    NativeContext.DirectZeta.LowValue.sourceValue_non_epsilon _ _ hc hε, hs.2]

/-- The real non-epsilon intermediate execution agrees with a real public
original-source-one lambda execution, retaining the original proper guard. -/
theorem execute_translation (a c out : Nat) (ha : SourceOneIota.rootCheck a = true)
    (ho : out ∈ NativeContext.DirectZeta.execute (alphaCode a) c)
    (hp : NativeContext.base (alphaCode a) < NativeContext.interpretation (alphaCode a) c)
    (hb : NativeContext.interpretation (alphaCode a) c < Enclosure.sourceAlphaPlus a)
    (hε : Ordinal.omega0 ^ NativeContext.interpretation (alphaCode a) c ≠ NativeContext.interpretation (alphaCode a) c) :
    ∃ other, other ∈ Lambda.PublicBranches.execute (returnedCode a c) ∧
      unionInterpretation other = NativeContext.interpretation (alphaCode a) out := by
  have hs := NativeContext.DirectZeta.execute_spec _ _ _ ho
  have hr := returnedCode_spec a c ha hs.1 hp hb
  obtain ⟨other, he⟩ := Lambda.PublicBranches.execute_returns _ hr.1
  have hne : ¬ Ordinal.omega0 ^ interpretation 0 (returnedCode a c) = interpretation 0 (returnedCode a c) := by
    simpa only [hr.2] using hε
  have hh : SourceOneIota.rootCheck (returnedCode a c) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hne ((Lambda.PublicBranches.high_iff_epsilon _ hr.1).mp h)
  have ht := (Lambda.PublicBranches.execute_spec _ other he).2.2
  simp only [Lambda.PublicBranches.sourceValue, hh, Bool.false_eq_true, if_false] at ht
  exact ⟨other, he, ht.trans ((zeta_value a c ha hs.1 hp hb hε).trans hs.2.2.2.symm)⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.BoundedContextLambda.LowTranslation
