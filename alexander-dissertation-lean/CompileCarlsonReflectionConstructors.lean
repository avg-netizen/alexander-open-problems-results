import Alexander313.Carlson.PrimitiveReflectionConstructorsExamples

/-!
# Reflection construction and original derived-code recursion gate

This gate compiles the new uniform target constructors and audits every new
public theorem. The independent conclusions below retain the original
pattern codecs on arbitrary raw inputs. The generic fold requires a certified
interpretation algebra; this gate does not claim a complete recursive
certificate decoder or checker.
-/

open Alexander313.Carlson
open Encodable Finite PrimitiveContinuityChecks PrimitiveReflectionConstructors

example (k : Bool) (n c a b s f : Nat) :
    constructDownward k n c a b s f =
      match decode (α := PatternCode n) c, decode (α := Fin n) a,
          decode (α := Fin n) b, decode (α := Finset (Fin n)) s,
          decode (α := Fin n → Fin n) f with
      | some C, some a', some b', some N, some g =>
          some (encode (C.downward (level k) a' b' N g))
      | _, _, _, _, _ => none := constructDownward_eq k n c a b s f

example (n c d a b s f : Nat) :
    constructUpward n c d a b s f =
      match decode (α := PatternCode n) c, decode (α := PatternCode n) d,
          decode (α := Fin n) a, decode (α := Fin n) b,
          decode (α := Finset (Fin n)) s, decode (α := Fin n → Fin n) f with
      | some C, some D, some a', some b', some N, some g =>
          some (encode (C.upward D a' b' N g))
      | _, _, _, _, _, _ => none := constructUpward_eq n c d a b s f

#print axioms Alexander313.Carlson.PrimitiveSExpression.left_lt
#print axioms Alexander313.Carlson.PrimitiveSExpression.right_lt
#print axioms Alexander313.Carlson.PrimitiveSExpression.fold_eq
#print axioms Alexander313.Carlson.PrimitiveSExpression.fold_atom
#print axioms Alexander313.Carlson.PrimitiveSExpression.fold_cons
#print axioms Alexander313.Carlson.PrimitiveSExpression.step_primrec
#print axioms Alexander313.Carlson.PrimitiveSExpression.step_history
#print axioms Alexander313.Carlson.PrimitiveSExpression.fold_primrec

#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.tabulate_eq
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.tabulate_primrec
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.back_primrec
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.back_view
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.downCore_primrec
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.downBridge_primrec
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.downwardData_primrec
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.downwardData_view
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.upCell_primrec
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.upwardData_primrec
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.upwardData_view
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.constructDownward_comp
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.constructUpward_comp
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.constructDownward_eq
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.constructUpward_eq
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.constructDownward_encode
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.constructUpward_encode
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.constructDownward_primrec
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.constructUpward_primrec
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.constructDownward_program
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructors.constructUpward_program

#print axioms Alexander313.Carlson.PrimitiveReflectionConstructorsExamples.downward_bridge_regression
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructorsExamples.upward_cross_regression
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructorsExamples.off_carrier_regression
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructorsExamples.raw_targets_regression
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructorsExamples.invalid_pattern_still_constructs
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructorsExamples.unsorted_carrier_regression
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructorsExamples.malformed_pattern_rejects
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructorsExamples.out_of_range_anchor_rejects
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructorsExamples.duplicate_carrier_rejects
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructorsExamples.malformed_total_map_rejects
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructorsExamples.empty_dimension_rejects
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructorsExamples.nodeCount_primrec
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructorsExamples.nested_recursion_regression
#print axioms Alexander313.Carlson.PrimitiveReflectionConstructorsExamples.downward_machine_regression

