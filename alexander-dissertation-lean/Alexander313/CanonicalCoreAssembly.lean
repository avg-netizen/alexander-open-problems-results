import Alexander313.CommonCoreAssembly
import Alexander313.Arithmetic.FiniteBounds

/-!
# Common-core assembly with the actual fixed universal arithmetic formula

The arithmetic formula and its coherence proof are the constructed canonical
objects, not source-presentation fields. `SourceFixedPoint` subsequently
constructs the effective family and exact presentation from an exact validity
program. `Delta.BLProofProgram.valid_program_exists` constructs that program;
`IdealGenericityInduction.family_sound` supplies global source soundness.
True canonical W numeral-instance PA certificates are derived here.
-/

namespace Alexander313

structure CanonicalCommonCorePresentation (R : Nat → Nat → Prop) where
  family : MachineFamily
  proofs : ∀ i θ, θ.Closed → (family.effective.proves i θ ↔
    Provable (PrefixedAxioms i
      (CommonCoreGenerator R (canonicalArithmeticCoding Nat) family i)) θ)

def CanonicalCommonCorePresentation.toCommonCorePresentation
    {R : Nat → Nat → Prop} (C : CanonicalCommonCorePresentation R) :
    CommonCorePresentation R where
  arithmetic := canonicalArithmeticCoding Nat
  family := C.family
  proofs := C.proofs

/-- A canonical specialization of the derived assembly, with no arithmetic
    object, coherence witness, trace-certificate theorem or target
    schema-membership premise supplied by the caller. This still does not
    construct C or its soundness. -/
theorem canonical_common_core_solution_nonempty (R : Nat → Nat → Prop)
    (C : CanonicalCommonCorePresentation R)
    (sound : ∀ i, RawSound C.family.effective.proves i) : Nonempty (Solution313 R) :=
  common_core_presentation_solution_nonempty R C.toCommonCorePresentation
    (canonicalArithmeticCodingCoherent Nat) canonicalArithmeticCoding_pa sound

end Alexander313
