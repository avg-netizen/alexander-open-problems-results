import Alexander313.Wilken.HereditaryGlobalMuDictionary
import Alexander313.Wilken.HereditaryGlobalAdditiveTrackingRelative

/-!
# Independent finite global reference and tracking sequences

Definition3.18 at lambda=0 has a genuine initial chain of finite upsilon
endpoints followed by strictly increasing epsilon entries in the initial
endpoint gap. Every cover uses the independently executing extended mu
of Definition3.15. These predicates are defined without an assignment or
evaluation. The source zero endpoint is literally zero, not finiteBase0.
Only the represented canonical finite-limit domain is claimed. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalTrackingSequences

open GlobalAdditiveTracking.Source (baseWord)
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceTrackingSequences (lastCode lastCode_mem)

abbrev endpointCode := PublicEpsilonSourceDictionary.endpointCode

noncomputable def muValue (a : Nat) : Ordinal.{0} :=
  unionInterpretation (GlobalMuDictionary.publicCode a)

inductive EpsilonReference : List Nat → Prop
  | nil : EpsilonReference []
  | one (a : Nat) (ha : GlobalMuDictionary.Support.inputCheck a = true) : EpsilonReference [a]
  | cons (a b : Nat) (xs : List Nat)
      (ha : GlobalMuDictionary.Support.inputCheck a = true)
      (hab : unionInterpretation a < unionInterpretation b)
      (hcover : unionInterpretation b ≤ muValue a)
      (ht : EpsilonReference (b :: xs)) : EpsilonReference (a :: b :: xs)

theorem EpsilonReference.nodes {xs : List Nat} (hr : EpsilonReference xs) :
    ∀ c ∈ xs, GlobalMuDictionary.Support.inputCheck c = true := by
  induction hr with
  | nil => intro c hc; exact False.elim (List.not_mem_nil hc)
  | one a ha => intro c hc; simpa only [List.mem_singleton.mp hc] using ha
  | cons a b xs ha hab hcover ht ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ha
    · exact ih c hc

theorem EpsilonReference.strict {xs : List Nat} (hr : EpsilonReference xs) :
    (xs.map unionInterpretation).Pairwise (· < ·) := by
  induction hr with
  | nil => simp only [List.map_nil, List.pairwise_nil]
  | one a ha => simp only [List.map_cons, List.map_nil, List.pairwise_singleton]
  | cons a b xs ha hab hcover ht ih =>
    rw [List.map_cons]
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro value hv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hab
    · exact hab.trans ((List.pairwise_cons.mp (show
        (unionInterpretation b :: xs.map unionInterpretation).Pairwise (· < ·) from
        by simpa only [List.map_cons] using ih)).1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩))

theorem EpsilonReference.of_relative {xs : List Nat}
    (hr : PublicTrackingSequences.Reference xs) : EpsilonReference xs := by
  induction hr with
  | nil => exact .nil
  | one a ha => exact .one a ((MuPublicDictionary.Support.inputCheck_exact a).mp ha).1
  | cons a b xs ha hab hcover ht ih =>
    refine .cons a b xs ((MuPublicDictionary.Support.inputCheck_exact a).mp ha).1 hab ?_ ih
    simpa only [muValue, GlobalMuDictionary.publicCode_proper a ha,
      SkPublicRecurrence.muValue] using hcover

def TailGap (m : Nat) (xs : List Nat) : Prop :=
  match xs with
  | [] => True
  | a :: _ => sourceUpsilon (m : Ordinal.{0}) < unionInterpretation a ∧
      unionInterpretation a < sourceUpsilon ((m + 1 : Nat) : Ordinal.{0})

def Reference (codes : List Nat) : Prop :=
  ∃ m : Nat, ∃ tail : List Nat, codes = baseWord m ++ tail ∧
    EpsilonReference tail ∧ TailGap m tail

theorem baseWord_length (m : Nat) : (baseWord m).length = m := by
  simp only [GlobalAdditiveTracking.Source.baseWord, List.length_map, List.length_range]

theorem reference_baseWord (m : Nat) : Reference (baseWord m) :=
  ⟨m, [], (List.append_nil _).symm, .nil, trivial⟩

theorem Reference.epsilons {codes : List Nat} (hr : Reference codes) :
    ∀ c ∈ codes, Canonical.check c = true ∧
      Ordinal.omega0 ^ unionInterpretation c = unionInterpretation c := by
  obtain ⟨m, tail, he, ht, hg⟩ := hr
  intro c hc
  rw [he] at hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    exact (GlobalMuDictionary.Support.inputCheck_exact _).mp
      (GlobalMuDictionary.Support.endpoint_input i)
  · exact (GlobalMuDictionary.Support.inputCheck_exact c).mp (ht.nodes c hc)

theorem Reference.last_mu_input {codes : List Nat} (hr : Reference codes) (hne : codes ≠ []) :
    GlobalMuDictionary.Support.inputCheck (lastCode codes) = true :=
  (GlobalMuDictionary.Support.inputCheck_exact _).mpr (hr.epsilons _ (lastCode_mem codes hne))

def Tracking (codes : List Nat) : Prop :=
  codes ≠ [] ∧ (∀ c ∈ codes, Canonical.check c = true) ∧ Reference (stripLast codes) ∧
    0 < unionInterpretation (lastCode codes) ∧
      Ordinal.IsPrincipal (· + ·) (unionInterpretation (lastCode codes)) ∧
        if stripLast codes = [] then
          1 ≤ unionInterpretation (lastCode codes) ∧
            unionInterpretation (lastCode codes) ≤ sourceUpsilon (1 : Ordinal.{0})
        else 1 < unionInterpretation (lastCode codes) ∧
          unionInterpretation (lastCode codes) ≤ muValue (lastCode (stripLast codes))

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalTrackingSequences
