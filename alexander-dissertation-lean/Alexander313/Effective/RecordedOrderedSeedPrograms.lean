import Alexander313.Effective.RecordedSeedPrograms
import Alexander313.Effective.RecordedOrderedBackgroundPrograms
import Alexander313.Effective.RecordedOrderedMainPrograms
import Alexander313.Effective.RecordedOrderedPrefixPrograms

/-!
# Full positive recorded compilation using executing label-order data

The constructed seven-row background, guarded main and indexed-prefix images
all use the same supplied order Program. Finite-consequence compilation is
then composed unchanged. Numerical ordering of label codes is not used for
semantic nesting, introspection or guards.

This does not construct Wilken's hereditary code domain or its order/R1/R2
algorithms. Exact original Valid and canonical source/hierarchy identification
also remain explicit semantic inputs. No local truth/genericity is concluded.
-/

noncomputable section

namespace Alexander313.OrderedRecordedSeedProgram

open RecordedFormula

abbrev Parameters := RecordedSeedProgram.Parameters × Program

def backgroundData (p : Parameters) : OrderedRecordedBackgroundProgram.Parameters :=
  (p.2, RecordedSeedProgram.backgroundData p.1)

theorem backgroundData_primrec : Primrec backgroundData :=
  Primrec.snd.pair (RecordedSeedProgram.backgroundData_primrec.comp Primrec.fst)

def mainData (p : Parameters) : OrderedRecordedMainProgram.Parameters := (p.1.1, p.2)

theorem mainData_primrec : Primrec mainData :=
  (Primrec.fst.comp Primrec.fst).pair Primrec.snd

def seed (p : Parameters) (a : Nat) (σ : Syntax) : Prop :=
  OrderedRecordedBackgroundProgram.admits (backgroundData p) a σ ∨
    OrderedRecordedMainProgram.admits (mainData p) a σ

theorem seed_closed {p : Parameters} {a : Nat} {σ : Syntax} (h : seed p a σ) : σ.Closed :=
  h.elim OrderedRecordedBackgroundProgram.admits_closed OrderedRecordedMainProgram.admits_closed

theorem seed_admissible {p : Parameters} {a : Nat} {σ : Syntax} (h : seed p a σ) :
    letI : LT Nat := Program.orderLT p.2
    σ.RecordedAdmissible p.1.1.1.1.toFinset p.1.1.1.2.toFinset :=
  h.elim OrderedRecordedBackgroundProgram.admits_admissible OrderedRecordedMainProgram.admits_admissible

theorem seed_exact {R : Nat → Nat → Prop} (C : CommonCorePresentation R) (p : Parameters)
    (hArithmetic : C.arithmetic = canonicalArithmeticCoding Nat)
    (hsource : C.family.effective.recognizes = p.1.1.2.1.1)
    (hhierarchy : ∀ j i, p.1.1.2.1.2.domain (Nat.pair j i) ↔ R j i)
    (hvalid : ∀ φ : Formula Nat, p.1.2.domain (φ.code id) ↔ Valid φ)
    (a : Nat) (σ : Syntax) :
    letI : LT Nat := Program.orderLT p.2
    seed p a σ ↔
      RecordedBackground p.1.1.1.1.toFinset p.1.1.1.2.toFinset a
        (fun μ ν => p.1.1.2.2.1.domain (Nat.pair μ ν)) σ ∨
      RecordedMain C p.1.1.1.1.toFinset p.1.1.1.2.toFinset a
        (fun μ ν => p.1.1.2.2.1.domain (Nat.pair μ ν))
        (fun μ ν => p.1.1.2.2.2.domain (Nat.pair μ ν)) σ := by
  letI : LT Nat := Program.orderLT p.2
  exact or_congr
    (OrderedRecordedBackgroundProgram.background_exact (backgroundData p)
      (fun μ ν => p.1.1.2.2.1.domain (Nat.pair μ ν)) (fun _ _ => Iff.rfl) hvalid a σ)
    (OrderedRecordedMainProgram.admits_exact C (mainData p) hArithmetic hsource hhierarchy a σ)

theorem seed_compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ p a σ, (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔ seed p a σ) ∧
    (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed ∧
        (letI : LT Nat := Program.orderLT p.2
         σ.RecordedAdmissible p.1.1.1.1.toFinset p.1.1.1.2.toFinset)) := by
  obtain ⟨background, hbg, exactBg, rawBg⟩ := OrderedRecordedBackgroundProgram.compiler_exists
  obtain ⟨main, hmain, exactMain, rawMain⟩ := OrderedRecordedMainProgram.compiler_exists
  obtain ⟨union, hunion, exactUnion⟩ := Program.finiteUnionCompiler_exists
  let table : Parameters → List Program :=
    fun p => [background (backgroundData p), main (mainData p)]
  have htable : Primrec table :=
    Primrec.list_cons.comp (hbg.comp backgroundData_primrec)
      (Primrec.list_cons.comp (hmain.comp mainData_primrec) (Primrec.const []))
  refine ⟨fun p => union (table p), hunion.comp htable, ?_, ?_⟩
  · intro p a σ
    rw [exactUnion]
    change (∃ d ∈ [background (backgroundData p), main (mainData p)],
      d.domain (Nat.pair a (σ.code RecordedHead.code))) ↔ _
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨d, rfl | rfl, hd⟩
      · exact Or.inl ((exactBg (backgroundData p) a σ).mp hd)
      · exact Or.inr ((exactMain (mainData p) a σ).mp hd)
    · rintro (hb | hm)
      · exact ⟨background (backgroundData p), Or.inl rfl, (exactBg (backgroundData p) a σ).mpr hb⟩
      · exact ⟨main (mainData p), Or.inr rfl, (exactMain (mainData p) a σ).mpr hm⟩
  · intro p query h
    obtain ⟨d, hd, ht⟩ := (exactUnion (table p) query).mp h
    change d ∈ [background (backgroundData p), main (mainData p)] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact rawBg (backgroundData p) query ht
    · exact rawMain (mainData p) query ht

def admissions (p : Parameters) (a : Nat) (σ : Syntax) : Prop :=
  letI : LT Nat := Program.orderLT p.2
  RecordedPrefixClosure p.1.1.1.1.toFinset a (seed p a) σ

theorem admissions_exact {R : Nat → Nat → Prop} (C : CommonCorePresentation R) (p : Parameters)
    (hArithmetic : C.arithmetic = canonicalArithmeticCoding Nat)
    (hsource : C.family.effective.recognizes = p.1.1.2.1.1)
    (hhierarchy : ∀ j i, p.1.1.2.1.2.domain (Nat.pair j i) ↔ R j i)
    (hvalid : ∀ φ : Formula Nat, p.1.2.domain (φ.code id) ↔ Valid φ)
    (a : Nat) (σ : Syntax) :
    letI : LT Nat := Program.orderLT p.2
    admissions p a σ ↔ FullRecordedAdmissions C p.1.1.1.1.toFinset p.1.1.1.2.toFinset a
      (fun μ ν => p.1.1.2.2.1.domain (Nat.pair μ ν))
      (fun μ ν => p.1.1.2.2.2.domain (Nat.pair μ ν)) σ := by
  letI : LT Nat := Program.orderLT p.2
  have hseed : seed p a = fun θ =>
      RecordedBackground p.1.1.1.1.toFinset p.1.1.1.2.toFinset a
        (fun μ ν => p.1.1.2.2.1.domain (Nat.pair μ ν)) θ ∨
      RecordedMain C p.1.1.1.1.toFinset p.1.1.1.2.toFinset a
        (fun μ ν => p.1.1.2.2.1.domain (Nat.pair μ ν))
        (fun μ ν => p.1.1.2.2.2.domain (Nat.pair μ ν)) θ := by
    funext θ
    exact propext (seed_exact C p hArithmetic hsource hhierarchy hvalid a θ)
  rw [admissions, hseed]
  exact (FullRecordedAdmissions.iff_prefixClosure C p.1.1.1.1.toFinset p.1.1.1.2.toFinset a
    (fun μ ν => p.1.1.2.2.1.domain (Nat.pair μ ν))
    (fun μ ν => p.1.1.2.2.2.domain (Nat.pair μ ν)) σ).symm

theorem admission_compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ p a σ, (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔ admissions p a σ) ∧
    (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed ∧
        (letI : LT Nat := Program.orderLT p.2
         σ.RecordedAdmissible p.1.1.1.1.toFinset p.1.1.1.2.toFinset)) := by
  obtain ⟨seeds, hseed, exactSeed, _⟩ := seed_compiler_exists
  obtain ⟨prefixes, hprefix, exactPrefix, rawPrefix⟩ := OrderedRecordedPrefixProgram.compiler_exists
  let parameters : Parameters → OrderedRecordedPrefixProgram.Parameters :=
    fun p => (p.2, (p.1.1.1, seeds p))
  have hp : Primrec parameters := Primrec.snd.pair
    ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair hseed)
  refine ⟨fun p => prefixes (parameters p), hprefix.comp hp, ?_, ?_⟩
  · intro p a σ
    exact (exactPrefix (parameters p) a σ).trans
      (OrderedRecordedPrefixProgram.closure_exact (parameters p) (seed p)
        (exactSeed p) (fun _ _ h => seed_closed h) (fun _ _ h => seed_admissible h) a σ)
  · intro p query h
    exact rawPrefix (parameters p) query h

theorem theory_compiler_exists : ∃ compiler : Parameters → Program, Primrec compiler ∧
    (∀ {R : Nat → Nat → Prop} (C : CommonCorePresentation R) (p : Parameters),
      C.arithmetic = canonicalArithmeticCoding Nat →
      C.family.effective.recognizes = p.1.1.2.1.1 →
      (∀ j i, p.1.1.2.1.2.domain (Nat.pair j i) ↔ R j i) →
      (∀ φ : Formula Nat, p.1.2.domain (φ.code id) ↔ Valid φ) → ∀ a σ,
        (compiler p).domain (Nat.pair a (σ.code RecordedHead.code)) ↔
          (letI : LT Nat := Program.orderLT p.2
           σ.Closed ∧ Provable
             (FullRecordedAdmissions C p.1.1.1.1.toFinset p.1.1.1.2.toFinset a
               (fun μ ν => p.1.1.2.2.1.domain (Nat.pair μ ν))
               (fun μ ν => p.1.1.2.2.2.domain (Nat.pair μ ν))) σ)) ∧
    (∀ p query, (compiler p).domain query → ∃ a, ∃ σ : Syntax,
      query = Nat.pair a (σ.code RecordedHead.code) ∧ σ.Closed) := by
  obtain ⟨generators, hgen, exactGen, _⟩ := admission_compiler_exists
  obtain ⟨consequences, hcon, exactCon, rawCon⟩ := RecordedConsequenceProgram.compiler_exists
  let parameters : Parameters → Program × Program := fun p => (generators p, p.1.2)
  have hp : Primrec parameters := hgen.pair (Primrec.snd.comp Primrec.fst)
  refine ⟨fun p => consequences (parameters p), hcon.comp hp, ?_, ?_⟩
  · intro R C p hArithmetic hsource hhierarchy hvalid a σ
    letI : LT Nat := Program.orderLT p.2
    exact (exactCon (generators p) p.1.2 a σ).trans
      (RecordedConsequenceProgram.generated_exact (generators p) p.1.2 hvalid
        (fun b θ => FullRecordedAdmissions C p.1.1.1.1.toFinset p.1.1.1.2.toFinset b
          (fun μ ν => p.1.1.2.2.1.domain (Nat.pair μ ν))
          (fun μ ν => p.1.1.2.2.2.domain (Nat.pair μ ν)) θ)
        (fun b θ => (exactGen p b θ).trans
          (admissions_exact C p hArithmetic hsource hhierarchy hvalid b θ))
        (fun _ _ h => h.closed) a σ)
  · intro p query h
    exact rawCon (parameters p) query h

end Alexander313.OrderedRecordedSeedProgram
