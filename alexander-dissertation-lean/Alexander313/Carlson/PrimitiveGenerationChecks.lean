import Alexander313.Carlson.PrimitiveRecursiveChecks

/-! Uniform verification of the original generation-by-restriction records. -/

namespace Alexander313.Carlson.PrimitiveGenerationChecks

open Encodable Finite PrimitiveCertificateAlgebra PrimitiveFiniteChecks
open PrimitiveRecursiveChecks (chainResult chainResult_primrec chainResult_encode
  emptySummary accepts accepts_primrec)

def generation (n : ℕ) (chain : Summary) (target : ℕ) : Summary :=
  (chain.1, target, chain.2.2 && checkSub n target chain.2.1 &&
    decide (carrier n chain.1 ⊆ carrier n target))

def generationSummary {n : ℕ} (c : GenerationCertificate n) : Summary :=
  (encode c.source, encode c.target, c.check)

variable {σ : Type*} [Primcodable σ]

theorem generation_primrec {n target : σ → ℕ} {chain : σ → Summary}
    (hn : Primrec n) (hc : Primrec chain) (ht : Primrec target) :
    Primrec (fun s => generation (n s) (chain s) (target s)) := by
  have hp := Primrec.fst.comp hc
  have hq := Primrec.fst.comp (Primrec.snd.comp hc)
  exact hp.pair (ht.pair (Primrec.and.comp
    (Primrec.and.comp (Primrec.snd.comp (Primrec.snd.comp hc))
      (checkSub_primrec.comp (hn.pair (ht.pair hq))))
    (PrimitiveFiniteOperations.finset_subset.comp
      (carrier_primrec hn hp) (carrier_primrec hn ht)).decide))

theorem generation_encode {n : ℕ} (c : GenerationCertificate n) :
    generation n (chainSummary c.chain) (encode c.target) = generationSummary c := by
  simp [generation, chainSummary, generationSummary, GenerationCertificate.source,
    GenerationCertificate.check, PatternCode.checkSub, carrierView_subset_iff,
    Bool.and_assoc]

theorem parse_pack (chain target : ℕ) :
    PrimitiveGenerationCodec.parse (PrimitiveGenerationCodec.pack chain target) =
      some (chain, target) := by
  simp [PrimitiveGenerationCodec.parse, PrimitiveGenerationCodec.pack,
    PrimitiveRationalPresentation.decodeField]

/-- This internal fold is applied only after original generation decoding. -/
def generationResult (n code : ℕ) : Summary :=
  ((PrimitiveGenerationCodec.parse code).map fun p =>
    generation n (chainResult n p.1) p.2).getD emptySummary

theorem generationResult_primrec : Primrec₂ generationResult := by
  apply Primrec₂.mk
  unfold generationResult
  refine Primrec.option_getD.comp
    (Primrec.option_map (PrimitiveGenerationCodec.parse_primrec.comp Primrec.snd) ?_)
    (Primrec.const emptySummary)
  exact (generation_primrec (Primrec.fst.comp Primrec.fst)
    (chainResult_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)).to₂

theorem generationResult_encode {n : ℕ} (c : GenerationCertificate n) :
    generationResult n (encode c) = generationSummary c := by
  simp only [generationResult, PrimitiveGenerationCodec.encode_generation, parse_pack,
    Option.map_some, Option.getD_some, chainResult_encode]
  exact generation_encode c

def summarizeGeneration (n code : ℕ) : Option Summary :=
  (PrimitiveGenerationCodec.normalize n code).map (generationResult n)

theorem summarizeGeneration_primrec : Primrec₂ summarizeGeneration :=
  (Primrec.option_map PrimitiveGenerationCodec.normalize_primrec
    (generationResult_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂

theorem summarizeGeneration_eq (n code : ℕ) :
    summarizeGeneration n code =
      (decode (α := GenerationCertificate n) code).map generationSummary := by
  unfold summarizeGeneration
  rw [PrimitiveGenerationCodec.normalize_eq]
  cases decode (α := GenerationCertificate n) code <;> simp [generationResult_encode]

@[simp] theorem summarizeGeneration_encode {n : ℕ} (c : GenerationCertificate n) :
    summarizeGeneration n (encode c) = some (generationSummary c) := by
  rw [summarizeGeneration_eq, Encodable.encodek]
  rfl

def checkGeneration (n p q code : ℕ) : Bool :=
  accepts (summarizeGeneration n code) p q

theorem checkGeneration_primrec {n p q code : σ → ℕ}
    (hn : Primrec n) (hp : Primrec p) (hq : Primrec q) (hc : Primrec code) :
    Primrec (fun s => checkGeneration (n s) (p s) (q s) (code s)) :=
  accepts_primrec (summarizeGeneration_primrec.comp hn hc) hp hq

theorem checkGeneration_encode_endpoints {n : ℕ} (P Q : PatternCode n) (code : ℕ) :
    checkGeneration n (encode P) (encode Q) code = Finite.checkGeneration P Q code := by
  unfold checkGeneration Finite.checkGeneration
  rw [summarizeGeneration_eq]
  cases decode (α := GenerationCertificate n) code <;>
    simp [PrimitiveRecursiveChecks.accepts, generationSummary, encode_inj]

theorem generation_summary_program : ∃ machine : Nat.Partrec.Code, ∀ n code : ℕ,
    machine.eval (Nat.pair n code) = Part.some (encode (summarizeGeneration n code)) := by
  obtain ⟨machine, hm⟩ := PrimitiveRationalPresentation.exists_code summarizeGeneration_primrec
  exact ⟨machine, fun n code => hm (n, code)⟩

theorem original_generationSummary_primrec (n : ℕ) : Primrec (@generationSummary n) :=
  Primrec.option_some_iff.mp
    ((summarizeGeneration_primrec.comp (Primrec.const n) Primrec.encode).of_eq
      fun c => summarizeGeneration_encode c)

theorem original_generationSource_primrec (n : ℕ) : Primrec (@GenerationCertificate.source n) :=
  Primrec.encode_iff.mp (Primrec.fst.comp (original_generationSummary_primrec n))

theorem original_generationTarget_primrec (n : ℕ) :
    Primrec (fun c : GenerationCertificate n => c.target) :=
  Primrec.encode_iff.mp
    (Primrec.fst.comp (Primrec.snd.comp (original_generationSummary_primrec n)))

theorem original_generationCheck_primrec (n : ℕ) : Primrec (@GenerationCertificate.check n) :=
  Primrec.snd.comp (Primrec.snd.comp (original_generationSummary_primrec n))

end Alexander313.Carlson.PrimitiveGenerationChecks
