import Alexander313.Effective.RecordedMainPrograms
import Alexander313.Effective.RecordedPrefixPrograms
import Alexander313.Effective.RecordedConsequencePrograms

/-!
# Actual recorded seed, full-admission and consequence compilers

The seed is the finite union of the constructed background and guarded-main
programs. Its indexed-prefix closure and finite-consequence compiler are then
constructed uniformly from ordinary executing program data. There is no
supplied seed program, finite-mask decision contract or guard-effectivity
contract in these constructions.

Semantic identification still requires canonical arithmetic coding, the
actual source-family program, an exact hierarchy-edge program and an exact
program for the original semantic `Valid`. The label type is `Nat` with its
ordinary order. This is not an implementation of Wilken's ordinal domain,
order or relations, and it does not discharge the full thesis obligations.
-/

noncomputable section

namespace Alexander313.RecordedSeedProgram

open RecordedFormula

abbrev Parameters := RecordedMainProgram.Parameters × Program

def backgroundData (p : Parameters) : RecordedBackgroundProgram.Parameters :=
  ((p.1.1, p.1.2.2.1), p.2)

theorem backgroundData_primrec : Primrec backgroundData := by
  have hmain : Primrec (fun p : Parameters => p.1) := Primrec.fst
  have hAE := Primrec.fst.comp hmain
  have hedges := Primrec.snd.comp (Primrec.snd.comp hmain)
  exact (hAE.pair (Primrec.fst.comp hedges)).pair Primrec.snd

def seed (p : Parameters) (a : Nat) (σ : Syntax) : Prop :=
  RecordedBackgroundProgram.admits (backgroundData p) a σ ∨
    RecordedMainProgram.admits p.1 a σ

theorem seed_closed {p : Parameters} {a : Nat} {σ : Syntax}
    (h : seed p a σ) : σ.Closed :=
  h.elim RecordedBackgroundProgram.admits_closed RecordedMainProgram.admits_closed

theorem seed_admissible {p : Parameters} {a : Nat} {σ : Syntax}
    (h : seed p a σ) : σ.RecordedAdmissible p.1.1.1.toFinset p.1.1.2.toFinset :=
  h.elim RecordedBackgroundProgram.admits_admissible RecordedMainProgram.admits_admissible

theorem seed_exact {R : Nat → Nat → Prop} (C : CommonCorePresentation R) (p : Parameters)
    (hArithmetic : C.arithmetic = canonicalArithmeticCoding Nat)
    (hsource : C.family.effective.recognizes = p.1.2.1.1)
    (hhierarchy : ∀ j i, p.1.2.1.2.domain (Nat.pair j i) ↔ R j i)
    (hvalid : ∀ φ : Formula Nat, p.2.domain (φ.code id) ↔ Valid φ)
    (a : Nat) (σ : Syntax) :
    seed p a σ ↔
      RecordedBackground p.1.1.1.toFinset p.1.1.2.toFinset a
        (fun μ ν => p.1.2.2.1.domain (Nat.pair μ ν)) σ ∨
      RecordedMain C p.1.1.1.toFinset p.1.1.2.toFinset a
        (fun μ ν => p.1.2.2.1.domain (Nat.pair μ ν))
        (fun μ ν => p.1.2.2.2.domain (Nat.pair μ ν)) σ := by
  exact or_congr
    (RecordedBackgroundProgram.background_exact (backgroundData p)
      (fun μ ν => p.1.2.2.1.domain (Nat.pair μ ν)) (fun _ _ => Iff.rfl) hvalid a σ)
    (RecordedMainProgram.admits_exact C p.1 hArithmetic hsource hhierarchy a σ)

/-- A uniform executing program for the actual background/main seed table.
    Exact-domain and raw-code statements do not require semantic soundness
    assumptions on the supplied source, hierarchy, validity or edge programs. -/
theorem seed_compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ p a σ, (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔ seed p a σ) ∧
    (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed ∧
        σ.RecordedAdmissible p.1.1.1.toFinset p.1.1.2.toFinset) := by
  obtain ⟨background, hbg, exactBg, rawBg⟩ := RecordedBackgroundProgram.compiler_exists
  obtain ⟨main, hmain, exactMain, rawMain⟩ := RecordedMainProgram.compiler_exists
  obtain ⟨union, hunion, exactUnion⟩ := Program.finiteUnionCompiler_exists
  let table : Parameters → List Program :=
    fun p => [background (backgroundData p), main p.1]
  have htable : Primrec table :=
    Primrec.list_cons.comp (hbg.comp backgroundData_primrec)
      (Primrec.list_cons.comp (hmain.comp Primrec.fst) (Primrec.const []))
  refine ⟨fun p => union (table p), hunion.comp htable, ?_, ?_⟩
  · intro p a σ
    rw [exactUnion]
    change (∃ d ∈ [background (backgroundData p), main p.1],
      d.domain (Nat.pair a (σ.code RecordedHead.code))) ↔ _
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨d, rfl | rfl, hd⟩
      · exact Or.inl ((exactBg (backgroundData p) a σ).mp hd)
      · exact Or.inr ((exactMain p.1 a σ).mp hd)
    · rintro (hb | hm)
      · exact ⟨background (backgroundData p), Or.inl rfl,
          (exactBg (backgroundData p) a σ).mpr hb⟩
      · exact ⟨main p.1, Or.inr rfl, (exactMain p.1 a σ).mpr hm⟩
  · intro p query h
    obtain ⟨d, hd, ht⟩ := (exactUnion (table p) query).mp h
    change d ∈ [background (backgroundData p), main p.1] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact rawBg (backgroundData p) query ht
    · exact rawMain p.1 query ht

def admissions (p : Parameters) (a : Nat) (σ : Syntax) : Prop :=
  RecordedPrefixClosure p.1.1.1.toFinset a (seed p a) σ

theorem admissions_exact {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    (p : Parameters)
    (hArithmetic : C.arithmetic = canonicalArithmeticCoding Nat)
    (hsource : C.family.effective.recognizes = p.1.2.1.1)
    (hhierarchy : ∀ j i, p.1.2.1.2.domain (Nat.pair j i) ↔ R j i)
    (hvalid : ∀ φ : Formula Nat, p.2.domain (φ.code id) ↔ Valid φ)
    (a : Nat) (σ : Syntax) :
    admissions p a σ ↔ FullRecordedAdmissions C p.1.1.1.toFinset p.1.1.2.toFinset a
      (fun μ ν => p.1.2.2.1.domain (Nat.pair μ ν))
      (fun μ ν => p.1.2.2.2.domain (Nat.pair μ ν)) σ := by
  have hseed : seed p a = fun θ =>
      RecordedBackground p.1.1.1.toFinset p.1.1.2.toFinset a
        (fun μ ν => p.1.2.2.1.domain (Nat.pair μ ν)) θ ∨
      RecordedMain C p.1.1.1.toFinset p.1.1.2.toFinset a
        (fun μ ν => p.1.2.2.1.domain (Nat.pair μ ν))
        (fun μ ν => p.1.2.2.2.domain (Nat.pair μ ν)) θ := by
    funext θ
    exact propext (seed_exact C p hArithmetic hsource hhierarchy hvalid a θ)
  rw [admissions, hseed]
  exact (FullRecordedAdmissions.iff_prefixClosure C p.1.1.1.toFinset p.1.1.2.toFinset a
    (fun μ ν => p.1.2.2.1.domain (Nat.pair μ ν))
    (fun μ ν => p.1.2.2.2.domain (Nat.pair μ ν)) σ).symm

/-- Compose the constructed seed and indexed-prefix compilers. In particular,
    an exact seed `Program` is not a premise of this theorem. -/
theorem admission_compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ p a σ, (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔ admissions p a σ) ∧
    (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed ∧
        σ.RecordedAdmissible p.1.1.1.toFinset p.1.1.2.toFinset) := by
  obtain ⟨seeds, hseed, exactSeed, _⟩ := seed_compiler_exists
  obtain ⟨prefixes, hprefix, exactPrefix, rawPrefix⟩ := RecordedPrefixProgram.compiler_exists
  let parameters : Parameters → RecordedPrefixProgram.Parameters :=
    fun p => (p.1.1, seeds p)
  have hp : Primrec parameters := (Primrec.fst.comp Primrec.fst).pair hseed
  refine ⟨fun p => prefixes (parameters p), hprefix.comp hp, ?_, ?_⟩
  · intro p a σ
    exact (exactPrefix (parameters p) a σ).trans
      (RecordedPrefixProgram.closure_exact (parameters p) (seed p)
        (exactSeed p) (fun _ _ h => seed_closed h) (fun _ _ h => seed_admissible h) a σ)
  · intro p query h
    exact rawPrefix (parameters p) query h

/-- Uniform finite-consequence compilation for the full Nat-labelled table.
    Semantic identification exposes all remaining source/arithmetic/hierarchy
    and original-validity inputs. It asserts neither ordinal effectivity nor
    the tracking/local-truth conclusions of the full thesis. -/
theorem theory_compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ {R : Nat → Nat → Prop} (C : CommonCorePresentation R) (p : Parameters),
      C.arithmetic = canonicalArithmeticCoding Nat →
      C.family.effective.recognizes = p.1.2.1.1 →
      (∀ j i, p.1.2.1.2.domain (Nat.pair j i) ↔ R j i) →
      (∀ φ : Formula Nat, p.2.domain (φ.code id) ↔ Valid φ) → ∀ a σ,
        (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔
          σ.Closed ∧ Provable
            (FullRecordedAdmissions C p.1.1.1.toFinset p.1.1.2.toFinset a
              (fun μ ν => p.1.2.2.1.domain (Nat.pair μ ν))
              (fun μ ν => p.1.2.2.2.domain (Nat.pair μ ν))) σ) ∧
    (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed) := by
  obtain ⟨generators, hgen, exactGen, _⟩ := admission_compiler_exists
  obtain ⟨consequences, hcon, exactCon, rawCon⟩ := RecordedConsequenceProgram.compiler_exists
  let parameters : Parameters → Program × Program := fun p => (generators p, p.2)
  have hp : Primrec parameters := hgen.pair Primrec.snd
  refine ⟨fun p => consequences (parameters p), hcon.comp hp, ?_, ?_⟩
  · intro R C p hArithmetic hsource hhierarchy hvalid a σ
    exact (exactCon (generators p) p.2 a σ).trans
      (RecordedConsequenceProgram.generated_exact (generators p) p.2 hvalid
        (fun b θ => FullRecordedAdmissions C p.1.1.1.toFinset p.1.1.2.toFinset b
          (fun μ ν => p.1.2.2.1.domain (Nat.pair μ ν))
          (fun μ ν => p.1.2.2.2.domain (Nat.pair μ ν)) θ)
        (fun b θ => (exactGen p b θ).trans
          (admissions_exact C p hArithmetic hsource hhierarchy hvalid b θ))
        (fun _ _ h => h.closed) a σ)
  · intro p query h
    exact rawCon (parameters p) query h

end Alexander313.RecordedSeedProgram
