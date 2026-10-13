import Alexander313.Wilken.HereditaryEvaluationBlocks

/-!
# Genuine normal-form callers of the final evaluation component

The actual principal logarithm supplies a canonical reduced MNF word.
Descending factors and real multiplicative closure show that a value
above its previous epsilon has first factor at least that epsilon. The
first factor is at most the whole input, so the genuine extended-mu
caller descends to this actual factor. The literal initial value one is
handled separately. No factorization or relative-assignment caller is
supplied to the final construction. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationFinalComponent.Support

open GlobalTrackingSequences EvaluationRelativeCallers
open Alexander313.Wilken.MultiplicativeNormalForm
open Alexander313.Wilken.MultiplicativeFactorRemoval (factorProduct_mem_le)
open Alexander313.Wilken.MultiplicativePrincipalArithmetic

def factors (beta : Nat) : Part (List Nat) :=
  (PrincipalLogarithm.logarithm beta).map MultiplicativeNormalForm.factorWord

theorem factors_partrec : Partrec factors :=
  Partrec.map PrincipalLogarithm.logarithm_partrec
    (MultiplicativeNormalForm.factorWord_primrec.comp Primrec.snd).to_comp.to₂

theorem factors_spec (beta : Nat) (word : List Nat) (ho : word ∈ factors beta) :
    MultiplicativeNormalForm.FormSpec beta word := by
  obtain ⟨d, hd, he⟩ := (Part.mem_map_iff _).mp ho
  rw [← he]
  exact MultiplicativeNormalForm.factorWord_spec beta d (PrincipalLogarithm.logarithm_graph beta d hd)

theorem factors_returns (beta : Nat) (hi : Principal.unionPrincipalCheck beta = true) :
    ∃ word, word ∈ factors beta := by
  obtain ⟨d, hd, _, _⟩ := PrincipalLogarithm.logarithm_returns beta hi
  exact ⟨MultiplicativeNormalForm.factorWord d, Part.mem_map _ hd⟩

def startCheck (gamma : Nat) : Bool :=
  (gamma == endpointCode 0) || GlobalMuDictionary.Support.inputCheck gamma

theorem startCheck_primrec : Primrec startCheck :=
  Primrec.or.comp (Primrec.beq.comp Primrec.id (Primrec.const _))
    GlobalMuDictionary.Support.inputCheck_primrec

theorem startCheck_exact (gamma : Nat) : startCheck gamma = true ↔
    gamma = endpointCode 0 ∨ GlobalMuDictionary.Support.inputCheck gamma = true := by
  simp only [startCheck, Bool.or_eq_true, beq_iff_eq]

theorem start_checked (gamma : Nat) (hi : startCheck gamma = true) : Canonical.check gamma = true := by
  rcases (startCheck_exact gamma).mp hi with rfl | hi
  · exact PublicEpsilonSourceDictionary.endpointCode_checked 0
  · exact ((GlobalMuDictionary.Support.inputCheck_exact gamma).mp hi).1

theorem start_one_le (gamma : Nat) (hi : startCheck gamma = true) : 1 ≤ unionInterpretation gamma := by
  rcases (startCheck_exact gamma).mp hi with rfl | hi
  · simp only [PublicEpsilonSourceDictionary.endpointCode_value, finiteBase_zero, le_refl]
  · exact (EpsilonOffsets.epsilon_one_lt ((GlobalMuDictionary.Support.inputCheck_exact gamma).mp hi).2).le

theorem factorProduct_lt (gamma : Ordinal.{0}) (hm : IsMultiplicativePrincipal gamma)
    (hone : 1 < gamma) (xs : List Ordinal.{0}) (hb : ∀ a ∈ xs, a < gamma) :
    factorProduct xs < gamma := by
  revert hb
  induction xs with
  | nil => intro hb; exact hone
  | cons a xs ih =>
    intro hb
    exact hm.2.2 (hb a List.mem_cons_self)
      (ih (fun b hm => hb b (List.mem_cons_of_mem _ hm)))

/-- The true first normal-form factor is bounded by its whole original
input and lies above the actual relative starting epsilon or one. -/
theorem first_factor_bounds (gamma beta first : Nat) (rest : List Nat)
    (hg : startCheck gamma = true)
    (hs : MultiplicativeNormalForm.FormSpec beta (first :: rest))
    (hgt : unionInterpretation gamma < unionInterpretation beta) :
    unionInterpretation gamma ≤ unionInterpretation first ∧
      unionInterpretation first ≤ unionInterpretation beta := by
  have hr := hs.2.2.1
  have hfirst : unionInterpretation first ∈ (first :: rest).map unionInterpretation :=
    List.mem_map.mpr ⟨first, List.mem_cons_self, rfl⟩
  refine ⟨?_, ?_⟩
  · rcases (startCheck_exact gamma).mp hg with he | he
    · rw [he, PublicEpsilonSourceDictionary.endpointCode_value, finiteBase_zero]
      exact (hr.2 _ hfirst).le
    · apply le_of_not_gt
      intro hsmall
      have heps := ((GlobalMuDictionary.Support.inputCheck_exact gamma).mp he).2
      have hm := NativeContext.SourceMultiplicativePrincipal.epsilon_multiplicative _ heps
      have hone := EpsilonOffsets.epsilon_one_lt heps
      have hb : ∀ a ∈ (first :: rest).map unionInterpretation, a < unionInterpretation gamma := by
        intro a ha
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hsmall
        · have ht := (List.pairwise_cons.mp (show
            (unionInterpretation first :: rest.map unionInterpretation).Pairwise (fun a b => b ≤ a)
            from by simpa only [List.map_cons] using hr.1.2)).1 _
              (List.mem_map.mpr ⟨c, hc, rfl⟩)
          exact ht.trans_lt hsmall
      have hp := factorProduct_lt _ hm hone _ hb
      rw [hs.2.2.2] at hp
      exact hgt.not_ge hp.le
  · have hp := factorProduct_mem_le _ (fun a ha => (hr.1.1 a ha).1) _ hfirst
    simpa only [hs.2.2.2] using hp

/-- A smaller genuinely canonical principal between the same real
floor and input inherits the original independently checked mu caller. -/
theorem block_caller_smaller (gamma beta delta : Nat)
    (hi : blockInputCheck gamma beta = true)
    (hc : Canonical.check delta = true) (hp : 0 < unionInterpretation delta)
    (ha : Ordinal.IsPrincipal (· + ·) (unionInterpretation delta))
    (hl : unionInterpretation gamma ≤ unionInterpretation delta)
    (hu : unionInterpretation delta ≤ unionInterpretation beta) :
    blockInputCheck gamma delta = true := by
  cases he : (gamma == endpointCode 0) with
  | true =>
    have ht : SourceOneRelativeAssignment.inputCheck beta = true := by
      simpa only [blockInputCheck, he, Bool.cond_true] using hi
    have hb := ((SourceOneRelativeAssignment.inputCheck_exact beta).mp ht).2.2.2
    simpa only [blockInputCheck, he, Bool.cond_true] using
      (SourceOneRelativeAssignment.inputCheck_exact delta).mpr ⟨hc, hp, ha, hu.trans hb⟩
  | false =>
    have ht : MuCoveredRelativeAssignment.Support.inputCheck gamma beta = true := by
      simpa only [blockInputCheck, he, Bool.cond_false] using hi
    have hb := (MuCoveredRelativeAssignment.Support.inputCheck_exact gamma beta).mp ht
    simpa only [blockInputCheck, he, Bool.cond_false] using
      (MuCoveredRelativeAssignment.Support.inputCheck_exact gamma delta).mpr
        ⟨hb.1, hc, hp, ha, hl, hu.trans hb.2.2.2.2.2⟩

theorem first_factor_caller (gamma beta first : Nat) (rest : List Nat)
    (hg : startCheck gamma = true) (hi : blockInputCheck gamma beta = true)
    (ho : (first :: rest) ∈ factors beta)
    (hgt : unionInterpretation gamma < unionInterpretation beta) :
    blockInputCheck gamma first = true := by
  have hs := factors_spec beta _ ho
  have hb := first_factor_bounds gamma beta first rest hg hs hgt
  have hm := hs.2.2.1.1.1 _ (List.mem_map.mpr ⟨first, List.mem_cons_self, rfl⟩)
  exact block_caller_smaller gamma beta first hi (hs.2.1 _ List.mem_cons_self)
    hm.1 hm.2.1 hb.1 hb.2

theorem factors_nonempty (gamma beta : Nat) (hg : startCheck gamma = true)
    (hgt : unionInterpretation gamma < unionInterpretation beta)
    (ho : [] ∈ factors beta) : False := by
  have he : unionInterpretation beta = 1 := (factors_spec beta [] ho).2.2.2.symm
  rw [he] at hgt
  exact hgt.not_ge (start_one_le gamma hg)

end Alexander313.Wilken.RelativeTerm.Hereditary.EvaluationFinalComponent.Support
