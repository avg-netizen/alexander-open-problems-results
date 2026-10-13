import Alexander313.Wilken.HereditaryGlobalTrackingAssignment
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingBounds

/-!
# The actual relative assignment at the literal initial base one

Definition3.35 uses alpha0=1 when its initial upsilon chain is empty.
Every independent canonical positive additive principal at most upsilon1
has the real original check-zero assignment. Strictly below upsilon1,
the genuine source return and complete original assignment execute.
At upsilon1 the printed upper-boundary extension is the literal singleton.
The exact caller and every original source witness are derived internally.
No Native base-one grammar or evaluation is supplied. Uncompiled sources.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneRelativeAssignment

open GlobalAdditiveTracking
open GlobalTrackingSequences (endpointCode)

def inputCheck (beta : Nat) : Bool :=
  Source.inputCheck beta && GlobalTrackingSequences.atMostFirstEndpointCheck beta

theorem inputCheck_primrec : Primrec inputCheck :=
  Primrec.and.comp Source.inputCheck_primrec
    GlobalTrackingSequences.atMostFirstEndpointCheck_primrec

theorem inputCheck_exact (beta : Nat) : inputCheck beta = true ↔
    Canonical.check beta = true ∧ 0 < unionInterpretation beta ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation beta) ∧
        unionInterpretation beta ≤ finiteBase 1 := by
  rw [inputCheck, Bool.and_eq_true, Source.inputCheck_exact,
    GlobalTrackingSequences.atMostFirstEndpointCheck_exact]
  constructor
  · rintro ⟨⟨hc, hp, ha⟩, hbound⟩
    exact ⟨hc, hp, ha, hbound.2.trans_eq (PublicUpsilonSegment.successor_value 0)⟩
  · rintro ⟨hc, hp, ha, hb⟩
    exact ⟨⟨hc, hp, ha⟩, hc, hb.trans_eq (PublicUpsilonSegment.successor_value 0).symm⟩

def boundaryCheck (beta : Nat) : Bool := beta == endpointCode 1

theorem boundaryCheck_primrec : Primrec boundaryCheck :=
  Primrec.beq.comp Primrec.id (Primrec.const _)

theorem boundaryCheck_exact (beta : Nat) (hi : inputCheck beta = true) :
    boundaryCheck beta = true ↔ unionInterpretation beta = finiteBase 1 := by
  rw [boundaryCheck, beq_iff_eq]
  constructor
  · intro he
    rw [he, PublicEpsilonSourceDictionary.endpointCode_value]
  · intro hv
    exact Canonical.check_value_injective _ _ ((inputCheck_exact beta).mp hi).1
      (PublicEpsilonSourceDictionary.endpointCode_checked 1)
      (hv.trans (PublicEpsilonSourceDictionary.endpointCode_value 1).symm)

theorem ordinary_bound (beta : Nat) (hi : inputCheck beta = true)
    (hb : boundaryCheck beta = false) : unionInterpretation beta < finiteBase 1 := by
  have hs := (inputCheck_exact beta).mp hi
  apply lt_of_le_of_ne hs.2.2.2
  intro he
  have ht := (boundaryCheck_exact beta hi).mpr he
  rw [hb] at ht
  cases ht

/-- The real least endpoint scan chooses level zero from the derived
strict first-endpoint bound, regardless of the stored public code level. -/
theorem ordinary_level_zero (beta : Nat) (hi : inputCheck beta = true)
    (hb : boundaryCheck beta = false) : Source.level beta = 0 := by
  by_contra hn
  have hlevel : 0 < PublicEpsilonSourceDictionary.level beta := Nat.pos_of_ne_zero hn
  have hfloor := (PublicEpsilonSourceDictionary.level_bound beta
    ((inputCheck_exact beta).mp hi).1).2.2 0 hlevel
  exact (ordinary_bound beta hi hb).not_ge hfloor

theorem source_caller (beta : Nat) (hi : inputCheck beta = true) :
    Source.inputCheck beta = true := (Bool.and_eq_true.mp hi).1

def execute (beta : Nat) : Part (List Nat) := cond (inputCheck beta)
  (cond (boundaryCheck beta) (Part.some [beta]) (Return.sourceOneExecute beta)) Part.none

theorem execute_partrec : Partrec execute :=
  Partrec.cond inputCheck_primrec.to_comp
    (Partrec.cond boundaryCheck_primrec.to_comp
      (Primrec.list_cons.comp Primrec.id (Primrec.const [])).to_comp.partrec
      Return.sourceOneExecute_partrec) Partrec.none

theorem execute_returns (beta : Nat) (hi : inputCheck beta = true) :
    ∃ out, out ∈ execute beta := by
  cases hb : boundaryCheck beta with
  | true =>
    refine ⟨[beta], ?_⟩
    simp only [execute, hi, hb, Bool.cond_true, Part.mem_some_iff]
  | false =>
    obtain ⟨out, ho⟩ := Return.sourceOneExecute_returns beta (source_caller beta hi)
      (ordinary_level_zero beta hi hb)
    exact ⟨out, by simpa only [execute, hi, hb, Bool.cond_true, Bool.cond_false] using ho⟩

theorem execute_domain (beta : Nat) : (execute beta).Dom ↔ inputCheck beta = true := by
  constructor
  · intro hd
    cases hi : inputCheck beta with
    | true => rfl
    | false =>
      have hn : (Part.none : Part (List Nat)).Dom := by
        simpa only [execute, hi, Bool.cond_false] using hd
      exact False.elim (Part.not_none_dom hn)
  · intro hi
    exact Part.dom_iff_mem.mpr (execute_returns beta hi)

/-- The complete assignment graph retains either the actual original
source-zero execution or its printed literal boundary singleton. -/
theorem execute_clauses (beta : Nat) (out : List Nat) : out ∈ execute beta ↔
    inputCheck beta = true ∧ ((boundaryCheck beta = true ∧ out = [beta]) ∨
      (boundaryCheck beta = false ∧ out ∈ Return.sourceOneExecute beta)) := by
  constructor
  · intro ho
    have hi := (execute_domain beta).mp (Part.dom_iff_mem.mpr ⟨out, ho⟩)
    refine ⟨hi, ?_⟩
    cases hb : boundaryCheck beta with
    | true => exact Or.inl ⟨hb, by simpa only
        [execute, hi, hb, Bool.cond_true, Part.mem_some_iff] using ho⟩
    | false => exact Or.inr ⟨hb, by simpa only
        [execute, hi, hb, Bool.cond_true, Bool.cond_false] using ho⟩
  · rintro ⟨hi, ⟨hb, rfl⟩ | ⟨hb, ho⟩⟩
    · simp only [execute, hi, hb, Bool.cond_true, Part.mem_some_iff]
    · simpa only [execute, hi, hb, Bool.cond_true, Bool.cond_false] using ho

theorem execute_tracking (beta : Nat) (out : List Nat) (ho : out ∈ execute beta) :
    PublicTrackingSequences.Tracking out := by
  obtain ⟨hi, hcases⟩ := (execute_clauses beta out).mp ho
  rcases hcases with ⟨hb, rfl⟩ | ⟨hb, ho⟩
  · have hs := (inputCheck_exact beta).mp hi
    exact PublicTrackingSequences.singleton_tracking beta hs.1 hs.2.1 hs.2.2.1
      (Order.one_le_iff_pos.mpr hs.2.1)
  · exact RelativeCertificate.sourceOneExecute_tracking beta out ho

theorem execute_ordinary_source (beta : Nat) (out : List Nat)
    (ho : out ∈ execute beta) (hb : boundaryCheck beta = false) :
    Theta.acceptedLowCode 0 (Source.sourceOneCode beta) = true ∧
      interpretation 0 (Source.sourceOneCode beta) = unionInterpretation beta ∧
        ∃ word, word ∈ SourceOneIota.SourceAdditiveTracking.Assignment.execute
          (Source.sourceOneCode beta) ∧ out = Return.sourceOneWord word ∧
            out.map unionInterpretation = word.map (interpretation 0) := by
  have hc := (execute_clauses beta out).mp ho
  have horiginal : out ∈ Return.sourceOneExecute beta := by
    simpa only [execute, hc.1, hb, Bool.cond_true, Bool.cond_false] using ho
  have hs := SourceZeta.Transport.returnCode_spec 0 beta ((inputCheck_exact beta).mp hc.1).1
    (ordinary_bound beta hc.1 hb)
  have hw := (Return.sourceOneExecute_spec beta out horiginal).2
  exact ⟨hs.1, hs.2, hw⟩

theorem execute_first_endpoint : [endpointCode 1] ∈ execute (endpointCode 1) := by
  have hc := PublicEpsilonSourceDictionary.endpointCode_checked 1
  have hv := PublicEpsilonSourceDictionary.endpointCode_value 1
  have he := finiteBase_succ_omegaPower_eq_self 0
  have hi : inputCheck (endpointCode 1) = true := (inputCheck_exact _).mpr
    ⟨hc, by rw [hv]; exact finiteBase_pos 1, by
      rw [hv, ← he]; exact Ordinal.isPrincipal_add_omega0_opow _, hv.le⟩
  have hb : boundaryCheck (endpointCode 1) = true := beq_self_eq_true _
  simp only [execute, hi, hb, Bool.cond_true, Part.mem_some_iff]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneRelativeAssignment
