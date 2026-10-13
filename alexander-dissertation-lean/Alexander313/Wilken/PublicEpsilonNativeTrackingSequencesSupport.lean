import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuLambdaBounds
import Alexander313.Wilken.SourceOneNativeMuLambdaBounds
import Alexander313.Wilken.HereditaryPrincipalClassification
import Alexander313.Wilken.HereditaryNativeUniformPublicReturn

/-!
# Actual principal and mu-cover checks for source tracking sequences

Original LOW callers are returned by the genuine uniform public producer.
Principal recognition uses the actual public canonical ANF. Mu comparison
uses the genuine original high-root producer at its actual target base,
followed by the proved canonical public return. Comparisons are finite
source computations, not semantic decisions or supplied mu/return oracles.
The original source-one adapter keeps its original check-zero dictionary.
No tracking evaluation, resemblance or length bound is asserted here.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceTrackingSequences.Support

open PublicEpsilonUnboundedIota

def principalCheck (q c : Nat) : Bool := lowCheckCode q c &&
  Principal.unionPrincipalCheck (UniformPublicReturn.publicCode q c)

theorem principalCheck_primrec : Primrec₂ principalCheck :=
  (Primrec.and.comp lowCheckCode_primrec
    (Principal.unionPrincipalCheck_primrec.comp UniformPublicReturn.publicCode_primrec)).to₂

theorem principalCheck_exact (q c : Nat) : principalCheck q c = true ↔
    lowCheckCode q c = true ∧ 0 < interpretation q c ∧
      Ordinal.IsPrincipal (· + ·) (interpretation q c) := by
  rw [principalCheck, Bool.and_eq_true, Principal.unionPrincipalCheck_exact]
  constructor
  · rintro ⟨hc, hpublic, hp, hprincipal⟩
    have hs := UniformPublicReturn.publicCode_spec q c
      ((UniformPublicReturn.inputCheck_exact q c).mpr hc)
    exact ⟨hc, by simpa only [hs.2] using hp, by simpa only [hs.2] using hprincipal⟩
  · rintro ⟨hc, hp, hprincipal⟩
    have hs := UniformPublicReturn.publicCode_spec q c
      ((UniformPublicReturn.inputCheck_exact q c).mpr hc)
    exact ⟨hc, Canonical.check_original hs.1,
      by simpa only [hs.2] using hp, by simpa only [hs.2] using hprincipal⟩

/-- Negating the genuine checked canonical comparison implements ordinal
less-or-equal in the reverse direction. Both code guards are proved. -/
theorem canonical_not_less_exact (a b : Nat) (ha : Canonical.check a = true)
    (hb : Canonical.check b = true) : !(Canonical.less a b) = true ↔
      unionInterpretation b ≤ unionInterpretation a := by
  constructor
  · intro h
    apply le_of_not_gt
    intro hlt
    have hl := (Canonical.less_exact a b).mpr ⟨ha, hb, hlt⟩
    simp only [hl, Bool.not_true, Bool.false_eq_true] at h
  · intro hle
    cases h : Canonical.less a b with
    | false => rfl
    | true => exact False.elim (((Canonical.less_exact a b).mp h).2.2.not_ge hle)

def muPublicCode (q root : Nat) : Nat :=
  UniformPublicReturn.publicCode (betaCode q root) (Mu.muCode q root)

theorem muPublicCode_primrec : Primrec (fun p : Nat × Nat => muPublicCode p.1 p.2) :=
  UniformPublicReturn.publicCode_primrec.comp betaCode_primrec Mu.muCode_primrec

theorem muPublicCode_spec (q root : Nat) (ha : Mu.inputCheck q root = true) :
    Canonical.check (muPublicCode q root) = true ∧
      unionInterpretation (muPublicCode q root) = Mu.sourceValue q root := by
  have hs := UniformPublicReturn.publicCode_spec (betaCode q root) (Mu.muCode q root)
    ((UniformPublicReturn.inputCheck_exact _ _).mpr (Mu.muCode_spec q root ha).1)
  exact ⟨hs.1, hs.2.trans (Mu.muCode_spec q root ha).2.2⟩

def coverCheck (q root next : Nat) : Bool :=
  (Mu.inputCheck q root && lowCheckCode q next) &&
    !(Canonical.less (muPublicCode q root) (UniformPublicReturn.publicCode q next))

theorem coverCheck_primrec : Primrec (fun p : (Nat × Nat) × Nat =>
    coverCheck p.1.1 p.1.2 p.2) := by
  have hq := Primrec.fst.comp Primrec.fst
  have hr := Primrec.snd.comp Primrec.fst
  have hnext := UniformPublicReturn.publicCode_primrec.comp hq Primrec.snd
  have hmu := muPublicCode_primrec.comp Primrec.fst
  exact Primrec.and.comp
    (Primrec.and.comp (Mu.inputCheck_primrec.comp Primrec.fst)
      (lowCheckCode_primrec.comp hq Primrec.snd))
    (Primrec.not.comp (Canonical.Effective.less_primrec.comp hmu hnext))

theorem coverCheck_exact (q root next : Nat) : coverCheck q root next = true ↔
    Mu.inputCheck q root = true ∧ lowCheckCode q next = true ∧
      interpretation q next ≤ Mu.sourceValue q root := by
  rw [coverCheck, Bool.and_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨ha, hn⟩, hle⟩
    have hm := muPublicCode_spec q root ha
    have hs := UniformPublicReturn.publicCode_spec q next
      ((UniformPublicReturn.inputCheck_exact q next).mpr hn)
    exact ⟨ha, hn, by simpa only [hm.2, hs.2] using
      (canonical_not_less_exact _ _ hm.1 hs.1).mp hle⟩
  · rintro ⟨ha, hn, hle⟩
    have hm := muPublicCode_spec q root ha
    have hs := UniformPublicReturn.publicCode_spec q next
      ((UniformPublicReturn.inputCheck_exact q next).mpr hn)
    exact ⟨⟨ha, hn⟩, (canonical_not_less_exact _ _ hm.1 hs.1).mpr
      (by simpa only [hm.2, hs.2] using hle)⟩

/-- Every genuine original high-root mu is at least omega. The strict
positive coefficient derives from the original root, rather than an oracle. -/
theorem omega_le_mu (q root : Nat) (ha : Mu.inputCheck q root = true) :
    Ordinal.omega0 ≤ Mu.sourceValue q root := by
  have hA := Lambda.coefficient_total_positive q root ha
  have hL := (Order.one_le_iff_pos.mpr hA).trans (MuSmallLambda.corrected_coefficient_le
    (interpretation (betaCode q root) (Mu.mappedCoefficient q root))
    (OmegaQuotient.coefficientOffset q root)
    (SourceChi.chiCode (betaCode q root) (Mu.mappedCoefficient q root)))
  have hp := omegaPower_strictMono.monotone hL
  rw [Ordinal.opow_one, ← Lambda.mu_corrected_value q root ha,
    (Mu.muCode_spec q root ha).2.2] at hp
  exact hp

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceTrackingSequences.Support

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceTrackingSupport

def muPublicCode (root : Nat) : Nat := NativeContext.UniformPublicReturn.publicCode
  (alphaCode root) (Mu.muCode root)

theorem muPublicCode_primrec : Primrec muPublicCode :=
  NativeContext.UniformPublicReturn.publicCode_primrec.comp alphaCode_primrec Mu.muCode_primrec

theorem muPublicCode_spec (root : Nat) (ha : Mu.inputCheck root = true) :
    Canonical.check (muPublicCode root) = true ∧
      unionInterpretation (muPublicCode root) = Mu.sourceValue root := by
  have hs := NativeContext.UniformPublicReturn.publicCode_spec (alphaCode root) (Mu.muCode root)
    ((NativeContext.UniformPublicReturn.inputCheck_exact _ _).mpr (Mu.muCode_spec root ha).1)
  exact ⟨hs.1, hs.2.trans (Mu.muCode_spec root ha).2.2⟩

/-- The original source-one high root has the same lower bound, using only
the real native target alpha; the original source remains check zero. -/
theorem omega_le_mu (root : Nat) (ha : Mu.inputCheck root = true) :
    Ordinal.omega0 ≤ Mu.sourceValue root := by
  have hA := Lambda.coefficient_total_positive root ha
  have hL := (Order.one_le_iff_pos.mpr hA).trans (MuSmallLambda.corrected_coefficient_le
    (NativeContext.interpretation (alphaCode root) (Mu.mappedCoefficient root))
    (OmegaQuotient.coefficientOffset root)
    (NativeContext.SourceChi.chiCode (alphaCode root) (Mu.mappedCoefficient root)))
  have hp := omegaPower_strictMono.monotone hL
  rw [Ordinal.opow_one, ← Lambda.mu_corrected_value root ha,
    (Mu.muCode_spec root ha).2.2] at hp
  exact hp

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceTrackingSupport
