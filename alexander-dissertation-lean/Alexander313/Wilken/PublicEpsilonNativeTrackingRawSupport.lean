import Alexander313.Wilken.PublicEpsilonNativeTrackingSequences
import Alexander313.Wilken.PublicEpsilonNativeContextTranslationSupport
import Alexander313.Wilken.PublicEpsilonNativeUnboundedMuValueInvariance

/-!
# Genuine original raw epsilon callers for tracking

The actual SAME-q normalizer/final-atom operation supplies a real original
HIGH root of the SAME value. Its finite guard recognizes precisely original
RAW LOW epsilons strictly above the base. The genuine mu spelling theorem
identifies the result with every admitted original root of that value.
No source3.8, parameter transport, public recoder or semantic decision is
supplied. Source-only candidates; no source-one tracking port is claimed.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceTrackingRaw.Support

open PublicEpsilonUnboundedIota

abbrev rootCode := ContextTranslation.Support.rootAtomCode

theorem rootCode_primrec : Primrec₂ rootCode := ContextTranslation.Support.rootAtomCode_primrec

def inputCheck (q c : Nat) : Bool := lowCheckCode q c &&
  (Mu.inputCheck q (rootCode q c) && Normalization.equalRawCode q (rootCode q c) c)

theorem inputCheck_primrec : Primrec₂ inputCheck := by
  have hr := rootCode_primrec
  exact (Primrec.and.comp lowCheckCode_primrec
    (Primrec.and.comp (Mu.inputCheck_primrec.comp (Primrec.fst.pair hr))
      (Normalization.Effective.equalRawCode_primrec.comp
        (Primrec.fst.pair (hr.pair Primrec.snd))))).to₂

theorem rootCode_spec (q c : Nat) (hc : inputCheck q c = true) :
    lowCheckCode q c = true ∧ Mu.inputCheck q (rootCode q c) = true ∧
      interpretation q (rootCode q c) = interpretation q c := by
  obtain ⟨hl, ht⟩ := Bool.and_eq_true.mp hc
  obtain ⟨hr, he⟩ := Bool.and_eq_true.mp ht
  exact ⟨hl, hr, ((Normalization.equalRawCode_exact q _ _).mp he).2.2⟩

/-- Every original raw LOW epsilon strictly above the base is accepted;
the original root representation is constructed, not supplied. -/
theorem inputCheck_exact (q c : Nat) : inputCheck q c = true ↔
    lowCheckCode q c = true ∧ base q < interpretation q c ∧
      Ordinal.omega0 ^ interpretation q c = interpretation q c := by
  constructor
  · intro hc
    have hs := rootCode_spec q c hc
    exact ⟨hs.1, by simpa only [hs.2.2] using Mu.root_base_lt q _ hs.2.1,
      by simpa only [hs.2.2] using RootLowCollapse.root_epsilon q _ hs.2.1⟩
  · rintro ⟨hl, hp, he⟩
    have hs := ContextTranslation.Support.rootAtomCode_spec q c hl hp he
    apply Bool.and_eq_true.mpr
    exact ⟨hl, Bool.and_eq_true.mpr ⟨hs.1,
      (Normalization.equalRawCode_exact q _ _).mpr
        ⟨RootLowCollapse.root_original q _ hs.1, (Bool.and_eq_true.mp hl).1, hs.2⟩⟩⟩

noncomputable def muValue (q c : Nat) : Ordinal.{0} := Mu.sourceValue q (rootCode q c)

/-- The selected actual root computes the genuine mu of EVERY original
admitted high-root spelling of this same raw epsilon value. -/
theorem muValue_eq (q c root : Nat) (hc : inputCheck q c = true)
    (hr : Mu.inputCheck q root = true) (hv : interpretation q c = interpretation q root) :
    muValue q c = Mu.sourceValue q root :=
  Mu.ValueInvariance.sourceValue_eq q _ root (rootCode_spec q c hc).2.1 hr
    ((rootCode_spec q c hc).2.2.trans hv)

theorem muValue_invariant (q c d : Nat) (hc : inputCheck q c = true)
    (hd : inputCheck q d = true) (hv : interpretation q c = interpretation q d) :
    muValue q c = muValue q d :=
  Mu.ValueInvariance.sourceValue_eq q _ _ (rootCode_spec q c hc).2.1
    (rootCode_spec q d hd).2.1
    ((rootCode_spec q c hc).2.2.trans (hv.trans (rootCode_spec q d hd).2.2.symm))

theorem omega_le_muValue (q c : Nat) (hc : inputCheck q c = true) :
    Ordinal.omega0 ≤ muValue q c :=
  SourceTrackingSequences.Support.omega_le_mu q _ (rootCode_spec q c hc).2.1

def rootWord (q : Nat) (xs : List Nat) : List Nat := xs.map (rootCode q)

theorem rootWord_primrec : Primrec₂ rootWord :=
  (Primrec.list_map Primrec.snd
    (rootCode_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂

theorem rootWord_values (q : Nat) (xs : List Nat)
    (hc : ∀ c ∈ xs, inputCheck q c = true) :
    (rootWord q xs).map (interpretation q) = xs.map (interpretation q) := by
  rw [rootWord, List.map_map]
  exact List.map_congr_left (fun c hm => (rootCode_spec q c (hc c hm)).2.2)

theorem rootWord_nodes (q : Nat) (xs : List Nat)
    (hc : ∀ c ∈ xs, inputCheck q c = true) :
    ∀ c ∈ rootWord q xs, Mu.inputCheck q c = true := by
  intro c hm
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
  exact (rootCode_spec q d (hc d hd)).2.1

theorem rootWord_nil (q : Nat) : rootWord q [] = [] := rfl

theorem rootWord_cons (q c : Nat) (xs : List Nat) :
    rootWord q (c :: xs) = rootCode q c :: rootWord q xs := rfl

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceTrackingRaw.Support
