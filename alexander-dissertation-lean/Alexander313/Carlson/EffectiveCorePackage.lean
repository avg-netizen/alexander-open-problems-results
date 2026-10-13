import Alexander313.Carlson.ComputableCoreEnumeration
import Alexander313.Carlson.CorePackageInputs

/-!
# The effective ordinal package on Carlson's actual common core

The explicit, duplicate-free enumeration supplies every natural label.
Its actual ordinal interpretation pulls back the linear order. The three
recognizing Programs are obtained from the proved computable comparison;
false answers diverge, as required by `Program.domain`. Reflection,
connectedness, separated guard room and finite tallness come from the
existing semantic core constructor, not from additional assumptions.
-/

namespace Alexander313.Carlson.EffectiveCorePackage

open ComputableCoreEnumeration

/-- Convert a total Boolean decision algorithm into a positive recognizer.
Returning false must not count as acceptance by `Program.domain`. -/
theorem recognizing_program (test : ℕ → Bool) (htest : Computable test) :
    ∃ machine : Program, ∀ n, machine.domain n ↔ test n = true := by
  let accept (n : ℕ) : Option ℕ := cond (test n) (some 0) none
  have haccept : Computable accept :=
    Computable.cond htest (Computable.const (some 0)) (Computable.const none)
  obtain ⟨machine, hm⟩ := Nat.Partrec.Code.exists_code.mp haccept.ofOption
  refine ⟨machine, fun n => ?_⟩
  change (machine.eval n).Dom ↔ test n = true
  rw [hm]
  cases hn : test n <;> simp [accept, hn]

/-- The package uses the ordinary natural pairing codec, with no validity
premise or omitted natural labels. -/
theorem binary_recognizing_program (test : ℕ → ℕ → Bool) (htest : Computable₂ test) :
    ∃ machine : Program, ∀ m n, machine.domain (Nat.pair m n) ↔ test m n = true := by
  let raw (z : ℕ) := test z.unpair.1 z.unpair.2
  have hraw : Computable raw := Computable.comp htest Primrec.unpair.to_comp
  obtain ⟨machine, hm⟩ := recognizing_program raw hraw
  exact ⟨machine, fun m n => by simpa only [raw, Nat.unpair_pair] using hm (Nat.pair m n)⟩

def less (m n : ℕ) : Bool := (ComputableCoreEnumeration.compare m n).2.2.1

def first (m n : ℕ) : Bool := (ComputableCoreEnumeration.compare m n).2.2.2.1

def second (m n : ℕ) : Bool := (ComputableCoreEnumeration.compare m n).2.2.2.2

theorem less_computable : Computable₂ less :=
  Computable.fst.comp (Computable.snd.comp (Computable.snd.comp compare_computable))

theorem first_computable : Computable₂ first :=
  Computable.fst.comp (Computable.snd.comp
    (Computable.snd.comp (Computable.snd.comp compare_computable)))

theorem second_computable : Computable₂ second :=
  Computable.snd.comp (Computable.snd.comp
    (Computable.snd.comp (Computable.snd.comp compare_computable)))

theorem less_correct (m n : ℕ) : less m n = true ↔ value m < value n :=
  (compare_correct m n).2.2.1

theorem first_correct (m n : ℕ) : first m n = true ↔ R1 (value m) (value n) :=
  (compare_correct m n).2.2.2.1

theorem second_correct (m n : ℕ) : second m n = true ↔ R2 (value m) (value n) :=
  (compare_correct m n).2.2.2.2

/-- The order is not the usual natural-number order. It is the pullback of
actual ordinal order along the explicit bijective interpretation. -/
noncomputable def order : LinearOrder ℕ := LinearOrder.lift' value value_injective

/-- Only the semantic section is chosen. All executable comparisons above
use the finite enumeration and never call this section or an ordinal oracle. -/
noncomputable def pre (a : Ordinal.{0}) : ℕ :=
  if h : a < coreBound then Classical.choose (value_surjective a h) else 0

theorem value_pre (a : Ordinal.{0}) (h : a < coreBound) : value (pre a) = a := by
  rw [pre, dif_pos h]
  exact Classical.choose_spec (value_surjective a h)

noncomputable def presentation : OrdinalPresentation (CodedLabel order) where
  val := value
  pre := pre
  bound := coreBound
  lt_iff := fun _ _ => Iff.rfl
  val_lt := value_lt_coreBound
  val_pre := value_pre

theorem presentation_bound : presentation.bound = coreBound := rfl

theorem less_program : ∃ machine : Program, ∀ m n : CodedLabel order,
    machine.domain (Nat.pair m n) ↔ m < n := by
  obtain ⟨machine, hm⟩ := binary_recognizing_program less less_computable
  exact ⟨machine, fun m n => (hm m n).trans (less_correct m n)⟩

theorem first_program : ∃ machine : Program, ∀ m n : CodedLabel order,
    machine.domain (Nat.pair m n) ↔ presentation.first m n := by
  obtain ⟨machine, hm⟩ := binary_recognizing_program first first_computable
  exact ⟨machine, fun m n => (hm m n).trans (first_correct m n)⟩

theorem second_program : ∃ machine : Program, ∀ m n : CodedLabel order,
    machine.domain (Nat.pair m n) ↔ presentation.second m n := by
  obtain ⟨machine, hm⟩ := binary_recognizing_program second second_computable
  exact ⟨machine, fun m n => (hm m n).trans (second_correct m n)⟩

/-- The final package has no effective-presentation, relation-program,
reflection, room or tallness parameter left to discharge. -/
theorem package_exists : Nonempty OrdinalPackage := by
  obtain ⟨ltMachine, hlt⟩ := less_program
  obtain ⟨firstMachine, hfirst⟩ := first_program
  obtain ⟨secondMachine, hsecond⟩ := second_program
  exact ⟨OrdinalPackage.ofCarlsonCore order presentation presentation_bound
    ltMachine firstMachine secondMachine hlt hfirst hsecond⟩

noncomputable def package : OrdinalPackage := Classical.choice package_exists

end Alexander313.Carlson.EffectiveCorePackage
