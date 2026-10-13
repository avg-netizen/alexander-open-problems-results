import Alexander313.Wilken.SourceOneNativeAdditiveTrackingBranchesOrderSupport

/-!
# Actual source-one factor frames at a common recursive prefix

Actual factor-program membership and complete assignment execution derive
the child and printed branch memberships. Two factor outputs at the same
literal original recursive prefix execute the SAME partial child, so
Part uniqueness identifies its actual word. The source product equations
derive increasing factors and the strengthened child last-factor bound
derives both honest joint callers. No child word, branch or lexical
comparison is an oracle. Different-prefix comparison remains separate.
Source-only uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.FrameFactorOrder

open NativeContext.SourceTrackingSequences (lastCode)

theorem actual_factor_child (current prefix factor : Nat) (out : List Nat)
    (hf : (prefix, factor) ∈ Factor.execute current)
    (ho : out ∈ Assignment.execute current) :
    ∃ heads, heads ∈ Assignment.execute prefix ∧ out ∈ Branches.execute (factor, heads) := by
  have hcheck := (Factor.execute_spec current (prefix, factor) hf).1
  have hfalse : SourceMultiplicativePrincipal.inputCheck current = false :=
    Bool.not_eq_true'.mp (Bool.and_eq_true.mp hcheck).2
  rcases Assignment.execute_clauses current out ho with ⟨hm, he⟩ |
    ⟨hm, child, last, heads, hc, hh, hb⟩
  · rw [hfalse] at hm
    cases hm
  · have he : (prefix, factor) = (child, last) := Part.mem_unique hf hc
    have hp : prefix = child := congrArg Prod.fst he
    have hl : factor = last := congrArg Prod.snd he
    subst child
    subst last
    exact ⟨heads, hh, hb⟩

/-- Complete actual executions at a common original written factor
prefix derive strict VALUE-word order from strict original input order.
All recursive child, factor and dispatcher callers are conclusions. -/
theorem execute_same_prefix_lex (leftInput rightInput prefix left right : Nat)
    (xs ys : List Nat)
    (hl : (prefix, left) ∈ Factor.execute leftInput)
    (hr : (prefix, right) ∈ Factor.execute rightInput)
    (hx : xs ∈ Assignment.execute leftInput)
    (hy : ys ∈ Assignment.execute rightInput)
    (hlt : interpretation 0 leftInput < interpretation 0 rightInput) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  obtain ⟨heads, hh, hbx⟩ := actual_factor_child leftInput prefix left xs hl hx
  obtain ⟨other, ht, hby⟩ := actual_factor_child rightInput prefix right ys hr hy
  have hheads : heads = other := Part.mem_unique hh ht
  subst other
  obtain ⟨_, _, hll, _, _, _, hml, _, hprodleft, _, _⟩ :=
    Factor.execute_spec leftInput (prefix, left) hl
  obtain ⟨_, _, hlr, _, _, _, hmr, _, hprodright, _, _⟩ :=
    Factor.execute_spec rightInput (prefix, right) hr
  have hs := (Assignment.execute_spec prefix heads hh).2.1
  have hbl := (Factor.Bounds.execute_last_le_prefix_last leftInput (prefix, left) hl).trans hs.2.2.1
  have hbr := (Factor.Bounds.execute_last_le_prefix_last rightInput (prefix, right) hr).trans hs.2.2.1
  have hf : interpretation 0 left < interpretation 0 right := by
    apply lt_of_not_ge
    intro he
    have hmul := mul_le_mul_right he (interpretation 0 prefix)
    exact hlt.not_ge (by rw [hprodleft, hprodright]; exact hmul)
  exact BranchesOrderSupport.execute_branches_lex heads hs.1 left right
    ((Theta.acceptedLowCode_iff 0 left).mp hll).1
    ((Theta.acceptedLowCode_iff 0 right).mp hlr).1 hml hmr hbl hbr hf xs ys hbx hby

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.FrameFactorOrder
