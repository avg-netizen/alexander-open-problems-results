import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingReplacementFidelity

/-!
# Actual conditional replacements of source Definition 3.20.2.2

The original computed comparison chooses precisely the raised M-word or
the literal singleton principal product. A head below the last factor is
necessarily in the actual proper epsilon prefix: the last head value is
at least that factor. Thus every raised caller follows from the original
checked headword. Both alternatives terminate and emit finite original
Normal LOW syntax. The small singleton need not itself be a q tracker
when its value lies below q; the insertion cover is proved separately.
No replacement, caller, product or tracking oracle. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ConditionalReplacement

open PublicEpsilonUnboundedIota SourceTrackingSequences
open Hereditary.FinePredecessor (stripLast)

abbrev Query := Replacement.Query

/-- Every written head of a checked raw tracking word is genuinely LOW,
positive and additive principal, including the final non-epsilon head. -/
theorem tracking_member_principal (q : Nat) (word : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q word = true) (head : Nat) (hh : head ∈ word) :
    lowCheckCode q head = true ∧ 0 < interpretation q head ∧
      Ordinal.IsPrincipal (· + ·) (interpretation q head) := by
  have hs := (SourceTrackingRaw.trackingCheck_conditions q word).mp hw
  obtain ⟨a, he, ha⟩ := Hereditary.FinePredecessor.stripLast_split word hs.1
  have hlast : lastCode word = a := by
    simp only [lastCode, ha, Option.getD_some]
  rw [he] at hh
  rcases List.mem_append.mp hh with hh | hh
  · have hr := (SourceTrackingRaw.Support.inputCheck_exact q head).mp (hs.2.1.nodes head hh)
    have hp := EpsilonOffsets.epsilon_pos_principal hr.2.2
    exact ⟨hr.1, hp.1, hp.2⟩
  · have hh : head = a := List.mem_singleton.mp hh
    subst head
    rw [← hlast]
    exact ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩

/-- The honest factor<=last-head inequality excludes the final position
from every raised branch and derives the original raw epsilon caller. -/
theorem raised_member_caller (q : Nat) (word : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q word = true) (head factor : Nat)
    (hh : head ∈ word) (hlt : interpretation q head < interpretation q factor)
    (hbound : interpretation q factor ≤ interpretation q (lastCode word)) :
    head ∈ stripLast word ∧ SourceTrackingRaw.Support.inputCheck q head = true := by
  have hs := (SourceTrackingRaw.trackingCheck_conditions q word).mp hw
  obtain ⟨a, he, ha⟩ := Hereditary.FinePredecessor.stripLast_split word hs.1
  have hlast : lastCode word = a := by simp only [lastCode, ha, Option.getD_some]
  have hm : head ∈ stripLast word := by
    rw [he] at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hh
    · have ha : head = a := List.mem_singleton.mp hh
      have hb : interpretation q factor ≤ interpretation q head := by
        simpa only [hlast, ha] using hbound
      exact False.elim (hlt.not_ge hb)
  exact ⟨hm, hs.2.1.nodes head hm⟩

def raisedCheck (q head factor : Nat) : Bool := Normalization.lessRawCode q head factor

theorem raisedCheck_primrec : Primrec (fun p : Query => raisedCheck p.1.1 p.1.2 p.2) :=
  Normalization.Effective.lessRawCode_primrec.comp
    ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))

theorem raisedCheck_exact (q head factor : Nat)
    (hh : lowCheckCode q head = true) (hf : lowCheckCode q factor = true) :
    raisedCheck q head factor = true ↔ interpretation q head < interpretation q factor := by
  constructor
  · intro he; exact ((Normalization.lessRawCode_exact q head factor).mp he).2.2
  · intro hlt
    exact (Normalization.lessRawCode_exact q head factor).mpr
      ⟨(Bool.and_eq_true.mp hh).1, (Bool.and_eq_true.mp hf).1, hlt⟩

def execute (q head factor : Nat) : Part (List Nat) := cond (raisedCheck q head factor)
  (Replacement.raisedReplacement q head factor) (Replacement.smallReplacement q head factor)

theorem execute_partrec : Partrec (fun p : Query => execute p.1.1 p.1.2 p.2) :=
  Partrec.cond raisedCheck_primrec.to_comp
    Replacement.raisedReplacement_partrec Replacement.smallReplacement_partrec

/-- Every original checked headword entry has a genuine terminating
printed replacement, with the head-only raised caller derived. -/
theorem execute_returns (q : Nat) (word : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q word = true) (head factor : Nat)
    (hh : head ∈ word) (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hbound : interpretation q factor ≤ interpretation q (lastCode word)) :
    ∃ out, out ∈ execute q head factor := by
  have hs := tracking_member_principal q word hw head hh
  cases hc : raisedCheck q head factor with
  | false =>
    simpa only [execute, hc, Bool.cond_false] using
      Replacement.smallReplacement_returns q head factor hs.1 hf
  | true =>
    have hlt := (raisedCheck_exact q head factor hs.1 hf).mp hc
    have hr := (raised_member_caller q word hw head factor hh hlt hbound).2
    simpa only [execute, hc, Bool.cond_true] using
      Replacement.raisedReplacement_returns q head factor hr hf hm hlt

/-- The output is exactly the computed raised replacement when factor
exceeds the written head, and otherwise the actual singleton head*factor.
All outputs are genuine original Normal LOW codes; no spelling identity
between source contexts or independent small-singleton tracker is claimed. -/
theorem execute_spec (q : Nat) (word : List Nat)
    (hw : SourceTrackingRaw.trackingCheck q word = true) (head factor : Nat)
    (hh : head ∈ word) (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hbound : interpretation q factor ≤ interpretation q (lastCode word))
    (out : List Nat) (ho : out ∈ execute q head factor) :
    out ≠ [] ∧ (∀ d ∈ out, lowCheckCode q d = true ∧ Comparison.acceptedCode q d = true) ∧
      ((interpretation q head < interpretation q factor ∧
          out ∈ Replacement.raisedReplacement q head factor ∧
          SourceTrackingRaw.trackingCheck q out = true) ∨
        (interpretation q factor ≤ interpretation q head ∧
          ∃ d, out = [d] ∧ interpretation q d = interpretation q head * interpretation q factor)) := by
  have hs := tracking_member_principal q word hw head hh
  cases hc : raisedCheck q head factor with
  | true =>
    have hlt := (raisedCheck_exact q head factor hs.1 hf).mp hc
    have hr := raised_member_caller q word hw head factor hh hlt hbound
    have ho : out ∈ Replacement.raisedReplacement q head factor := by
      simpa only [execute, hc, Bool.cond_true] using ho
    have ht := Replacement.raisedReplacement_spec q head factor out hr.2 hf hm hlt ho
    obtain ⟨raised, hra, htracking, hv, hlen, hchecked⟩ := ht
    have hne : out ≠ [] := by
      intro he
      have hn := ((trackingCheck_exact _ raised).mp htracking).1
      apply hn
      have hz : raised.length = 0 := by simpa only [he, List.length_nil] using hlen.symm
      exact List.length_eq_zero_iff.mp hz
    exact ⟨hne, fun d hd => ⟨(hchecked d hd).1, (hchecked d hd).2.1⟩,
      Or.inl ⟨hlt, ho, ReplacementFidelity.raisedReplacement_tracking q head factor word out
        hw hr.1 hf hm hlt hbound ho⟩⟩
  | false =>
    have hle : interpretation q factor ≤ interpretation q head := by
      apply le_of_not_gt
      intro hlt
      have he := (raisedCheck_exact q head factor hs.1 hf).mpr hlt
      rw [hc] at he
      cases he
    have ho : out ∈ Replacement.smallReplacement q head factor := by
      simpa only [execute, hc, Bool.cond_false] using ho
    obtain ⟨d, rfl, hl, hn, hv⟩ := Replacement.smallReplacement_spec q head factor out ho hs.2.1 hs.2.2 hm
    exact ⟨List.cons_ne_nil _ _, fun a ha => by
      rw [List.mem_singleton.mp ha]; exact ⟨hl, hn⟩, Or.inr ⟨hle, d, rfl, hv⟩⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ConditionalReplacement
