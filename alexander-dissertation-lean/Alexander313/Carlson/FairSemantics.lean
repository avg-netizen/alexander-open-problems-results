import Alexander313.Carlson.FairUpward
import Alexander313.Carlson.FairConverse
import Alexander313.Carlson.ReflectionConditions
import Alexander313.Carlson.FairSecondConverse

/-!
# Semantic characterization of covered fair limits

Carlson, *Patterns of resemblance of order 2*, Lemma 14.8(7--8), pure
case. The finite-stage relations on a fair union satisfy the intrinsic
reflection conditions. Coveredness supplies the converse through finite
covering rigidity. The statements quantify over the actual limit carrier.
-/

noncomputable section

namespace Alexander313.Carlson
namespace GeneratingSequence

variable {S : GeneratingSequence ℚ}

/-- The first relation of a covered fair union is exactly the first
semantic finite-copy condition together with the order bound. -/
theorem Fair.rel_one_iff (hS : S.Fair) (hP : Str.Covered (S.stage 0))
    (a b : S.Limit) :
    S.limitRel .one a b ↔ a ≤ b ∧
      FirstCondition (S.limitRel .one) (S.limitRel .two) a b :=
  ⟨fun h => ⟨S.rel_le h, hS.firstCondition h⟩,
    fun h => S.firstCondition_rel_one hP h.1 h.2⟩

/-- All clauses of the intrinsic second condition follow from a
second-relation edge in a fair union. Coveredness is unnecessary. -/
theorem Fair.secondCondition (hS : S.Fair) {a b : S.Limit}
    (h : S.limitRel .two a b) :
    SecondCondition (S.limitRel .one) (S.limitRel .two) a b :=
  ⟨S.rel_le h, hS.linkedCondition h, hS.cofinalCondition h⟩

/-- The second relation of a covered fair union is exactly Carlson's
linked-copy and upward-cofinality condition. -/
theorem Fair.rel_two_iff (hS : S.Fair) (hP : Str.Covered (S.stage 0))
    (a b : S.Limit) :
    S.limitRel .two a b ↔ SecondCondition (S.limitRel .one) (S.limitRel .two) a b :=
  ⟨hS.secondCondition, hS.secondCondition_rel_two hP⟩

end GeneratingSequence
end Alexander313.Carlson
