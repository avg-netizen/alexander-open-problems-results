import Alexander313.Wilken.SourceOneNativeMuValueInvariance
import Alexander313.Wilken.PublicEpsilonNativeTrackingSequencesSupport
import Alexander313.Wilken.HereditaryLogEndZero

/-!
# Actual original source-one RAW epsilon and principal tracking callers

The ORIGINAL check-zero normalizer and its actual last ANF atom construct
a Normal HIGH theta-zero root of every admitted raw LOW epsilon above one.
The original complete ANF, parameter admission, LOW sort and epsilon theorem
derive the caller; no Native base-one parser is used. The actual original
mu spelling theorem supplies a representation-independent mu value.
Canonical public tagging and genuine checked comparisons implement the
principal and mu-cover tests. Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceTrackingRaw.Support

open ThetaCourse

theorem original_checked (c : Nat) (hc : lowCheckCode 0 c = true) :
    checkCode 0 c = true :=
  (Bool.and_eq_true.mp (by simpa only [lowCheckCode_eq] using hc)).1

theorem original_bound (c : Nat) (hc : lowCheckCode 0 c = true) :
    interpretation 0 c < finiteBase 1 :=
  (lt_nextBase_iff_code 0 _).mpr ⟨c, hc, rfl⟩

def rootCode (c : Nat) : Nat :=
  LogEndZero.publicEndCode 0 (Theta.Normalization.normalizeCode 0 c)

theorem rootCode_primrec : Primrec rootCode :=
  LogEndZero.publicEndCode_primrec.comp (Primrec.const 0)
    (Theta.Normalization.Effective.normalizeCode_primrec.comp (Primrec.const 0) Primrec.id)

/-- The genuine original last-atom parser constructs the HIGH root on
the full raw LOW epsilon domain; a root-shaped input is not assumed. -/
theorem rootCode_high (c : Nat) (hc : lowCheckCode 0 c = true)
    (hp : 1 < interpretation 0 c)
    (he : Ordinal.omega0 ^ interpretation 0 c = interpretation 0 c) :
    rootCheck (rootCode c) = true ∧ interpretation 0 (rootCode c) = interpretation 0 c := by
  let n := Theta.Normalization.normalizeCode 0 c
  have hn := Theta.Normalization.normalizeCode_acceptedLow 0 c hc
  have hl := (Theta.acceptedLowCode_iff 0 n).mp hn.1
  have hi : SourceDecomposition.inputCheck 0 n = true :=
    (SourceDecomposition.inputCheck_exact 0 n).mpr ⟨original_checked n hl.1, hl.2⟩
  have hpos : 0 < interpretation 0 c := zero_lt_one.trans hp
  have hprincipal : Ordinal.IsPrincipal (· + ·) (interpretation 0 c) := by
    rw [← he]
    exact Ordinal.isPrincipal_add_omega0_opow _
  have hw := SourceDecomposition.word_spec 0 n hi
  have hmap : (SourceDecomposition.word 0 n).map (denote 0) = [interpretation 0 c] := by
    rw [hw.2, hn.2, canonicalANF_principal hpos hprincipal]
  have hlen : (SourceDecomposition.word 0 n).length = 1 := by
    simpa only [List.length_map, List.length_singleton] using congrArg List.length hmap
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.mp hlen
  have hm : t ∈ SourceDecomposition.word 0 n := by rw [ht]; exact List.mem_singleton_self _
  have hs := hw.1 t hm
  have hv : denote 0 t = interpretation 0 c := by
    simpa only [ht, List.map_singleton, List.singleton_inj] using hmap
  have hatom : LogEndZero.publicEndAtom 0 n = t := by
    simp only [LogEndZero.publicEndAtom, ht, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.getElem?_cons_zero, Option.getD_some]
  have hr : rootCode c = t.code := congrArg RelativeTerm.code hatom
  have hout : t.outerSort ≤ 1 := (denote_lt_iff_outerSort_le 0 t hs.1 1 (by omega)).mp (by
    rw [hv]
    exact (original_bound c hc).trans (finiteBase_lt_cardinal 0))
  rcases SourceDecomposition.word_shape 0 n t hm with ⟨p, rfl⟩ | ⟨k, a, rfl⟩
  · have had := Theta.checked_admissible 0 (SourceOne.PublicCodes.fragment (.parameter p))
      (.parameter p) hs.1 (SourceOne.PublicCodes.height_le_fragment _)
    have hb : denote 0 (.parameter p) < finiteBase 0 := parameter_sound _ p had.1
    rw [hv, finiteBase_zero] at hb
    exact False.elim (hp.not_ge hb.le)
  · have hk : k = 0 := by simp only [RelativeTerm.outerSort] at hout; omega
    subst k
    have hh : 1 < a.outerSort := by
      have hx := (Epsilon.theta_epsilon_iff 0 0 a hs.1).mp (by rw [hv]; exact he)
      simpa only [Nat.zero_add, Nat.lt_irrefl, or_self, and_false, or_false] using hx
    exact ⟨(rootCheck_exact _).mpr ⟨a, hr, hs.1, hs.2.1, hh⟩,
      by rw [hr, interpretation_code, hv]⟩

def inputCheck (c : Nat) : Bool := lowCheckCode 0 c &&
  (Mu.inputCheck (rootCode c) && Theta.Normalization.equalRawCode 0 (rootCode c) c)

theorem inputCheck_primrec : Primrec inputCheck :=
  Primrec.and.comp (Uniform.hereditaryLowCheckCode_primrec.comp (Primrec.const 0) Primrec.id)
    (Primrec.and.comp (Mu.inputCheck_primrec.comp rootCode_primrec)
      (Theta.Normalization.Effective.equalRawCode_primrec.comp
        ((Primrec.const 0).pair (rootCode_primrec.pair Primrec.id))))

theorem rootCode_spec (c : Nat) (hc : inputCheck c = true) :
    lowCheckCode 0 c = true ∧ Mu.inputCheck (rootCode c) = true ∧
      interpretation 0 (rootCode c) = interpretation 0 c := by
  obtain ⟨hl, ht⟩ := Bool.and_eq_true.mp hc
  obtain ⟨hr, he⟩ := Bool.and_eq_true.mp ht
  exact ⟨hl, hr, (Theta.Normalization.equalRawCode_correct 0 _ _
    (root_original _ hr) (original_checked c hl)).mp he⟩

theorem inputCheck_exact (c : Nat) : inputCheck c = true ↔
    lowCheckCode 0 c = true ∧ 1 < interpretation 0 c ∧
      Ordinal.omega0 ^ interpretation 0 c = interpretation 0 c := by
  constructor
  · intro hc
    have hs := rootCode_spec c hc
    exact ⟨hs.1, by rw [← hs.2.2]; exact EpsilonOffsets.epsilon_one_lt (root_epsilon _ hs.2.1),
      by rw [← hs.2.2]; exact root_epsilon _ hs.2.1⟩
  · rintro ⟨hl, hp, he⟩
    have hs := rootCode_high c hl hp he
    exact Bool.and_eq_true.mpr ⟨hl, Bool.and_eq_true.mpr ⟨hs.1,
      (Theta.Normalization.equalRawCode_correct 0 _ _
        (root_original _ hs.1) (original_checked c hl)).mpr hs.2⟩⟩

noncomputable def muValue (c : Nat) : Ordinal.{0} := Mu.sourceValue (rootCode c)

theorem muValue_eq (c root : Nat) (hc : inputCheck c = true)
    (hr : Mu.inputCheck root = true) (hv : interpretation 0 c = interpretation 0 root) :
    muValue c = Mu.sourceValue root :=
  Mu.ValueInvariance.sourceValue_eq _ root (rootCode_spec c hc).2.1 hr
    ((rootCode_spec c hc).2.2.trans hv)

theorem muValue_invariant (c d : Nat) (hc : inputCheck c = true)
    (hd : inputCheck d = true) (hv : interpretation 0 c = interpretation 0 d) :
    muValue c = muValue d :=
  Mu.ValueInvariance.sourceValue_eq _ _ (rootCode_spec c hc).2.1 (rootCode_spec d hd).2.1
    ((rootCode_spec c hc).2.2.trans (hv.trans (rootCode_spec d hd).2.2.symm))

theorem omega_le_muValue (c : Nat) (hc : inputCheck c = true) :
    Ordinal.omega0 ≤ muValue c :=
  SourceTrackingSupport.omega_le_mu _ (rootCode_spec c hc).2.1

def publicCode (c : Nat) : Nat := Canonical.canonicalize (Nat.pair 0 c)

theorem publicCode_primrec : Primrec publicCode :=
  Canonical.Effective.canonicalize_primrec.comp (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id)

theorem publicCode_spec (c : Nat) (hc : lowCheckCode 0 c = true) :
    Canonical.check (publicCode c) = true ∧ unionInterpretation (publicCode c) = interpretation 0 c := by
  have ht : unionCheck (Nat.pair 0 c) = true := by simpa only [unionCheck_pair] using hc
  exact ⟨Canonical.canonicalize_check _ ht,
    (Canonical.canonicalize_value _ ht).trans (by rw [unionInterpretation_pair])⟩

def principalCheck (c : Nat) : Bool := lowCheckCode 0 c && Principal.unionPrincipalCheck (publicCode c)

theorem principalCheck_primrec : Primrec principalCheck :=
  Primrec.and.comp (Uniform.hereditaryLowCheckCode_primrec.comp (Primrec.const 0) Primrec.id)
    (Principal.unionPrincipalCheck_primrec.comp publicCode_primrec)

theorem principalCheck_exact (c : Nat) : principalCheck c = true ↔
    lowCheckCode 0 c = true ∧ 0 < interpretation 0 c ∧
      Ordinal.IsPrincipal (· + ·) (interpretation 0 c) := by
  rw [principalCheck, Bool.and_eq_true, Principal.unionPrincipalCheck_exact]
  constructor
  · rintro ⟨hc, hp, hpos, hprincipal⟩
    have hs := publicCode_spec c hc
    exact ⟨hc, by simpa only [hs.2] using hpos, by simpa only [hs.2] using hprincipal⟩
  · rintro ⟨hc, hpos, hprincipal⟩
    have hs := publicCode_spec c hc
    exact ⟨hc, Canonical.check_original hs.1, by simpa only [hs.2] using hpos,
      by simpa only [hs.2] using hprincipal⟩

def coverCheck (root next : Nat) : Bool := (inputCheck root && lowCheckCode 0 next) &&
  !(Canonical.less (SourceTrackingSupport.muPublicCode (rootCode root)) (publicCode next))

theorem coverCheck_primrec : Primrec₂ coverCheck :=
  (Primrec.and.comp (Primrec.and.comp (inputCheck_primrec.comp Primrec.fst)
    (Uniform.hereditaryLowCheckCode_primrec.comp (Primrec.const 0) Primrec.snd))
    (Primrec.not.comp (Canonical.Effective.less_primrec.comp
      (SourceTrackingSupport.muPublicCode_primrec.comp (rootCode_primrec.comp Primrec.fst))
      (publicCode_primrec.comp Primrec.snd)))).to₂

theorem coverCheck_exact (root next : Nat) : coverCheck root next = true ↔
    inputCheck root = true ∧ lowCheckCode 0 next = true ∧ interpretation 0 next ≤ muValue root := by
  rw [coverCheck, Bool.and_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨hc, hn⟩, he⟩
    have hm := SourceTrackingSupport.muPublicCode_spec _ (rootCode_spec root hc).2.1
    have hs := publicCode_spec next hn
    exact ⟨hc, hn, by simpa only [hm.2, hs.2, muValue] using
      (NativeContext.SourceTrackingSequences.Support.canonical_not_less_exact _ _ hm.1 hs.1).mp he⟩
  · rintro ⟨hc, hn, he⟩
    have hm := SourceTrackingSupport.muPublicCode_spec _ (rootCode_spec root hc).2.1
    have hs := publicCode_spec next hn
    exact ⟨⟨hc, hn⟩,
      (NativeContext.SourceTrackingSequences.Support.canonical_not_less_exact _ _ hm.1 hs.1).mpr
        (by simpa only [hm.2, hs.2, muValue] using he)⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceTrackingRaw.Support
