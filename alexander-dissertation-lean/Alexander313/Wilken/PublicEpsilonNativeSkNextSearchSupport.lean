import Alexander313.Wilken.PublicEpsilonNativeSkNextStep
import Alexander313.Wilken.HereditaryFactorTruncation
import Mathlib.Computability.Partrec

/-!
# Actual finite LOW return search for a computed truncation

The search tests actual native LOW and Normal admission and literal equality
of its genuine canonical public return with the requested public code.
Real LOW boundary coverage and the actual normalizer prove termination on
every admitted canonical query in the native LOW interval. No representative
or return oracle is supplied. The search is partial recursive; no primitive
recursive search bound or syntactic parameter preservation is claimed.
The mu truncation caller and its true bound are derived below. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.Support

abbrev Query := Context × Nat

def candidate (q publicCode d : Nat) : Bool :=
  (lowCheckCode q d && Comparison.acceptedCode q d) &&
    (UniformPublicReturn.publicCode q d == publicCode)

theorem candidate_primrec : Primrec₂ (fun p : Nat × Nat => candidate p.1 p.2) := by
  have hq := Primrec.fst.comp Primrec.fst
  have hp := Primrec.snd.comp Primrec.fst
  have hu := UniformPublicReturn.publicCode_primrec.comp hq Primrec.snd
  exact (Primrec.and.comp
    (Primrec.and.comp (lowCheckCode_primrec.comp hq Primrec.snd)
      (Comparison.acceptedCode_primrec.comp hq Primrec.snd))
    (Primrec.beq.comp hu hp)).to₂

theorem candidate_exact (q publicCode d : Nat) : candidate q publicCode d = true ↔
    lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true ∧
      Canonical.check publicCode = true ∧ interpretation q d = unionInterpretation publicCode := by
  constructor
  · intro ht
    obtain ⟨hh, he⟩ := Bool.and_eq_true.mp ht
    obtain ⟨hl, hn⟩ := Bool.and_eq_true.mp hh
    have hs := UniformPublicReturn.publicCode_spec q d
      ((UniformPublicReturn.inputCheck_exact q d).mpr hl)
    have hc : UniformPublicReturn.publicCode q d = publicCode := beq_iff_eq.mp he
    exact ⟨hl, hn, hc ▸ hs.1, hs.2.symm.trans (congrArg unionInterpretation hc)⟩
  · rintro ⟨hl, hn, hp, hv⟩
    have hs := UniformPublicReturn.publicCode_spec q d
      ((UniformPublicReturn.inputCheck_exact q d).mpr hl)
    exact Bool.and_eq_true.mpr ⟨Bool.and_eq_true.mpr ⟨hl, hn⟩, beq_iff_eq.mpr
      (Canonical.check_value_injective _ _ hs.1 hp (hs.2.trans hv))⟩

def search (q publicCode : Nat) : Part Nat :=
  Nat.rfind (fun d => Part.some (candidate q publicCode d))

theorem search_partrec : Partrec₂ search :=
  (Partrec.rfind candidate_primrec.to_comp.partrec.to₂).to₂

theorem search_spec (q publicCode d : Nat) (hd : d ∈ search q publicCode) :
    lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true ∧
      Canonical.check publicCode = true ∧ interpretation q d = unionInterpretation publicCode :=
  (candidate_exact q publicCode d).mp ((Part.mem_some_iff.mp (Nat.rfind_spec hd)).symm)

theorem search_returns (q publicCode : Nat) (hq : baseCheck q = true)
    (hp : Canonical.check publicCode = true)
    (hb : unionInterpretation publicCode < globalBoundary (base q) 0) :
    ∃ d, d ∈ search q publicCode := by
  obtain ⟨c, hc, hv⟩ := (lt_boundary_iff_code q hq (unionInterpretation publicCode)).mp hb
  have hcheck : checkCode q c = true := (Bool.and_eq_true.mp hc).1
  have hn := Normalization.normalizeCode_accepted q c hcheck
  have hlow := OmegaPowers.low_of_bound q _ ((Comparison.acceptedCode_exact q _).mp hn.1).1
    (by rw [hn.2]; exact (HeightBoundary.input_spec q c hc).2.2)
  have ht := (candidate_exact q publicCode (Normalization.normalizeCode q c)).mpr
    ⟨hlow, hn.1, hp, hn.2.trans hv⟩
  have hdom : (search q publicCode).Dom := Nat.rfind_dom.mpr
    ⟨Normalization.normalizeCode q c, by simpa only [Part.mem_some_iff] using ht.symm,
      fun {_} _ => trivial⟩
  exact Part.dom_iff_mem.mp hdom

/-- The search domain is the actual canonical native LOW interval. -/
theorem search_domain (q publicCode : Nat) : (search q publicCode).Dom ↔
    baseCheck q = true ∧ Canonical.check publicCode = true ∧
      unionInterpretation publicCode < globalBoundary (base q) 0 := by
  constructor
  · intro hd
    obtain ⟨d, hd⟩ := Part.dom_iff_mem.mp hd
    have hs := search_spec q publicCode d hd
    have hq := (HeightBoundary.input_spec q d hs.1).2.1
    exact ⟨hq, hs.2.2.1, hs.2.2.2 ▸ checked_low_bound q d hs.1⟩
  · rintro ⟨hq, hp, hb⟩
    exact Part.dom_iff_mem.mpr (search_returns q publicCode hq hp hb)

def muPublicCode (q root : Nat) : Nat :=
  UniformPublicReturn.publicCode (betaCode q root) (Mu.muCode q root)

theorem muPublicCode_primrec : Primrec (fun p : Context => muPublicCode p.1 p.2) :=
  UniformPublicReturn.publicCode_primrec.comp betaCode_primrec Mu.muCode_primrec

theorem muPublicCode_spec (q root : Nat) (ha : Mu.inputCheck q root = true) :
    Canonical.check (muPublicCode q root) = true ∧
      unionInterpretation (muPublicCode q root) = Mu.sourceValue q root := by
  have hs := UniformPublicReturn.publicCode_spec (betaCode q root) (Mu.muCode q root)
    ((UniformPublicReturn.inputCheck_exact _ _).mpr (Mu.muCode_spec q root ha).1)
  exact ⟨hs.1, hs.2.trans (Mu.muCode_spec q root ha).2.2⟩

theorem muPublicCode_principal (q root : Nat) (ha : Mu.inputCheck q root = true) :
    Principal.unionPrincipalCheck (muPublicCode q root) = true := by
  have hs := muPublicCode_spec q root ha
  apply (Principal.unionPrincipalCheck_exact _).mpr
  rw [hs.2]
  exact ⟨Canonical.check_original hs.1, SkNextStep.mu_pos_principal q root⟩

theorem truncation_spec (q root cutoff out : Nat) (ha : Mu.inputCheck q root = true)
    (ho : out ∈ FactorTruncation.truncate (muPublicCode q root) cutoff) :
    Canonical.check out = true ∧
      unionInterpretation out = SkNextStep.nextValue q root (unionInterpretation cutoff) := by
  have hs := FactorTruncation.truncate_value _ _ out ho
  exact ⟨hs.2.2.1, hs.2.2.2.trans (by rw [(muPublicCode_spec q root ha).2]; rfl)⟩

theorem truncation_search_returns (q root cutoff out : Nat) (ha : Mu.inputCheck q root = true)
    (ho : out ∈ FactorTruncation.truncate (muPublicCode q root) cutoff) :
    ∃ d, d ∈ search (betaCode q root) out := by
  have hs := truncation_spec q root cutoff out ha ho
  exact search_returns _ out (betaCode_baseCheck q root ha) hs.1 (by
    rw [hs.2]
    exact SkNextStep.nextValue_boundary q root ha (unionInterpretation cutoff))

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.Support
