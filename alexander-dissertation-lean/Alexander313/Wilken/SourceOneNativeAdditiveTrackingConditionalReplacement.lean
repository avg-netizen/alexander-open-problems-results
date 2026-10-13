import Alexander313.Wilken.SourceOneNativeAdditiveTrackingReplacementFidelity
import Alexander313.Wilken.SourceOneNativeAdditiveTrackingProduct

/-!
# Actual conditional replacements in the original source-one dictionary

The original check-zero comparison chooses the genuine raised word or
the executing original singleton product. The honest factor<=headword-final
bound derives every raised proper-prefix caller. Both branches return
Normal LOW original syntax and real original RAW tracking words. Their
first value is at least the unchanged written head. No Native base-one
parser, supplied replacement, endpoint or tracking-assignment oracle.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ConditionalReplacement

open NativeContext.SourceTrackingSequences (lastCode lastCode_singleton)
open Hereditary.FinePredecessor (stripLast)

abbrev Query := Nat × Nat

def firstCode (word : List Nat) : Nat := word.head?.getD 0

theorem firstCode_primrec : Primrec firstCode :=
  Primrec.option_getD.comp Primrec.list_head? (Primrec.const 0)

theorem tracking_member_principal (word : List Nat)
    (hw : SourceTrackingRaw.trackingCheck word = true) (head : Nat) (hh : head ∈ word) :
    lowCheckCode 0 head = true ∧ 0 < interpretation 0 head ∧
      Ordinal.IsPrincipal (· + ·) (interpretation 0 head) := by
  have hs := (SourceTrackingRaw.trackingCheck_exact word).mp hw
  obtain ⟨a, he, ha⟩ := Hereditary.FinePredecessor.stripLast_split word hs.1
  have hlast : lastCode word = a := by simp only [lastCode, ha, Option.getD_some]
  rw [he] at hh
  rcases List.mem_append.mp hh with hh | hh
  · have hr := (SourceTrackingRaw.Support.inputCheck_exact head).mp (hs.2.1.nodes head hh)
    have hp := EpsilonOffsets.epsilon_pos_principal hr.2.2
    exact ⟨hr.1, hp.1, hp.2⟩
  · have hh : head = a := List.mem_singleton.mp hh
    subst head
    rw [← hlast]
    exact ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩

theorem raised_member_caller (word : List Nat)
    (hw : SourceTrackingRaw.trackingCheck word = true) (head factor : Nat)
    (hh : head ∈ word) (hlt : interpretation 0 head < interpretation 0 factor)
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode word)) :
    head ∈ stripLast word ∧ SourceTrackingRaw.Support.inputCheck head = true := by
  have hs := (SourceTrackingRaw.trackingCheck_exact word).mp hw
  obtain ⟨a, he, ha⟩ := Hereditary.FinePredecessor.stripLast_split word hs.1
  have hlast : lastCode word = a := by simp only [lastCode, ha, Option.getD_some]
  have hm : head ∈ stripLast word := by
    rw [he] at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hh
    · have ha : head = a := List.mem_singleton.mp hh
      have hf : interpretation 0 factor ≤ interpretation 0 head := by
        simpa only [hlast, ha] using hb
      exact False.elim (hlt.not_ge hf)
  exact ⟨hm, hs.2.1.nodes head hm⟩

def raisedCheck (head factor : Nat) : Bool := Theta.Normalization.lessRawCode 0 head factor

theorem raisedCheck_primrec : Primrec₂ raisedCheck :=
  (Theta.Normalization.Effective.lessRawCode_primrec.comp
    ((Primrec.const 0).pair (Primrec.fst.pair Primrec.snd))).to₂

theorem raisedCheck_exact (head factor : Nat)
    (hh : lowCheckCode 0 head = true) (hf : lowCheckCode 0 factor = true) :
    raisedCheck head factor = true ↔ interpretation 0 head < interpretation 0 factor :=
  Theta.Normalization.lessRawCode_correct 0 head factor
    (SourceTrackingRaw.Support.original_checked head hh)
    (SourceTrackingRaw.Support.original_checked factor hf)

def execute (head factor : Nat) : Part (List Nat) := cond (raisedCheck head factor)
  (Replacement.raisedReplacement head factor) (Product.smallReplacement head factor)

theorem execute_partrec : Partrec₂ execute := by
  have h : Partrec (fun p : Query => execute p.1 p.2) :=
    Partrec.cond raisedCheck_primrec.to_comp
      Replacement.raisedReplacement_partrec Product.smallReplacement_partrec
  exact h.to₂

theorem execute_returns (word : List Nat)
    (hw : SourceTrackingRaw.trackingCheck word = true) (head factor : Nat)
    (hh : head ∈ word) (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode word)) :
    ∃ out, out ∈ execute head factor := by
  have hs := tracking_member_principal word hw head hh
  cases hc : raisedCheck head factor with
  | false =>
    simpa only [execute, hc, Bool.cond_false] using
      Product.smallReplacement_returns head factor hs.1 hf
  | true =>
    have hlt := (raisedCheck_exact head factor hs.1 hf).mp hc
    have hr := (raised_member_caller word hw head factor hh hlt hb).2
    simpa only [execute, hc, Bool.cond_true] using
      Replacement.raisedReplacement_returns head factor hr hf

/-- The genuinely raised assignment starts above its own original head:
either the singleton is the larger factor, or its first proper root is
above that real raised base. Every returned first value is derived. -/
theorem raised_first_bound (head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hlt : interpretation 0 head < interpretation 0 factor)
    (ho : out ∈ Replacement.raisedReplacement head factor) :
    interpretation 0 head ≤ interpretation 0 (firstCode out) := by
  obtain ⟨raised, hr, rfl⟩ := (Part.mem_map_iff _).mp ho
  have hs := ReplacementSupport.raisedWord_spec head factor raised hh hf hm hlt hr
  have ht := (NativeContext.SourceTrackingSequences.trackingCheck_exact _ raised).mp hs.1
  cases raised with
  | nil => exact False.elim (ht.1 rfl)
  | cons c cs =>
    have hc := hs.2.2 c List.mem_cons_self
    have hd := SkSourcePathSupport.entryCode_spec _ c hc.1 hc.2.2
    have hfirst : interpretation 0 head <
        NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) c := by
      cases cs with
      | nil =>
        have hv : NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) c =
            interpretation 0 factor := by simpa only [lastCode_singleton] using hs.2.1
        rw [hv]; exact hlt
      | cons b bs =>
        have hp := ht.2.1
        rw [NativeContext.PublicEpsilonUnboundedIota.SkTracking.Support.stripLast_cons_nonempty
          c (b :: bs) (List.cons_ne_nil _ _)] at hp
        have hv := NativeContext.PublicEpsilonUnboundedIota.Mu.root_base_lt _ c hp.first
        simpa only [(ReplacementSupport.raisedBaseCode_spec head hh).2.1] using hv
    simpa only [Replacement.returnWord, List.map_cons, firstCode, List.head?_cons,
      Option.getD_some, hd.2] using hfirst.le

/-- Original source-one singleton products are themselves trackers,
including the genuine factor-one case, since their base floor is one. -/
theorem small_tracking (head factor : Nat) (out : List Nat)
    (ho : out ∈ Product.smallReplacement head factor)
    (hh : 0 < interpretation 0 head)
    (hp : Ordinal.IsPrincipal (· + ·) (interpretation 0 head))
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor)) :
    SourceTrackingRaw.trackingCheck out = true ∧
      interpretation 0 head ≤ interpretation 0 (firstCode out) := by
  obtain ⟨d, rfl, hd, hv⟩ := Product.smallReplacement_spec head factor out ho
  have hle : interpretation 0 head ≤ interpretation 0 d := by
    rw [hv]; exact Ordinal.le_mul_left _ hm.1
  have hpos := hh.trans_le hle
  have hprincipal : Ordinal.IsPrincipal (· + ·) (interpretation 0 d) := by
    rw [hv]
    by_cases he : interpretation 0 factor = 1
    · rw [he, Ordinal.mul_one]; exact hp
    · exact Ordinal.isPrincipal_add_mul_of_isPrincipal_add (interpretation 0 head) he hm.2.1
  exact ⟨SkTracking.Support.singleton_tracking d ((Theta.acceptedLowCode_iff 0 d).mp hd).1
    hpos hprincipal (Order.one_le_iff_pos.mpr hpos),
    by simpa only [firstCode, List.head?_cons, Option.getD_some] using hle⟩

/-- Both actual alternatives are genuine original RAW trackers, with
Normal LOW output and first>=head. The only raised-domain bound is the
honestly explicit factor<=original headword-final inequality. -/
theorem execute_spec (word : List Nat)
    (hw : SourceTrackingRaw.trackingCheck word = true) (head factor : Nat)
    (hh : head ∈ word) (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hb : interpretation 0 factor ≤ interpretation 0 (lastCode word))
    (out : List Nat) (ho : out ∈ execute head factor) :
    out ≠ [] ∧ (∀ d ∈ out, Theta.acceptedLowCode 0 d = true) ∧
      SourceTrackingRaw.trackingCheck out = true ∧
      interpretation 0 head ≤ interpretation 0 (firstCode out) ∧
      ((interpretation 0 head < interpretation 0 factor ∧
          out ∈ Replacement.raisedReplacement head factor) ∨
        (interpretation 0 factor ≤ interpretation 0 head ∧
          ∃ d, out = [d] ∧ interpretation 0 d = interpretation 0 head * interpretation 0 factor)) := by
  have hs := tracking_member_principal word hw head hh
  cases hc : raisedCheck head factor with
  | true =>
    have hlt := (raisedCheck_exact head factor hs.1 hf).mp hc
    have hr := raised_member_caller word hw head factor hh hlt hb
    have ho : out ∈ Replacement.raisedReplacement head factor := by
      simpa only [execute, hc, Bool.cond_true] using ho
    obtain ⟨raised, hra, he, ht, hv, hlen, hchecked⟩ :=
      Replacement.raisedReplacement_spec head factor out hr.2 hf hm hlt ho
    have htracking := ReplacementFidelity.raisedReplacement_tracking head factor word out
      hw hr.1 hf hm hlt hb ho
    exact ⟨((SourceTrackingRaw.trackingCheck_exact out).mp htracking).1,
      fun d hd => (hchecked d hd).1, htracking,
      raised_first_bound head factor out hr.2 hf hm hlt ho, Or.inl ⟨hlt, ho⟩⟩
  | false =>
    have hle : interpretation 0 factor ≤ interpretation 0 head := by
      apply le_of_not_gt
      intro hlt
      have he := (raisedCheck_exact head factor hs.1 hf).mpr hlt
      rw [hc] at he
      cases he
    have ho : out ∈ Product.smallReplacement head factor := by
      simpa only [execute, hc, Bool.cond_false] using ho
    have htracking := small_tracking head factor out ho hs.2.1 hs.2.2 hm
    obtain ⟨d, rfl, hd, hv⟩ := Product.smallReplacement_spec head factor out ho
    exact ⟨List.cons_ne_nil _ _, fun a ha => by rw [List.mem_singleton.mp ha]; exact hd,
      htracking.1, htracking.2, Or.inr ⟨hle, d, rfl, hv⟩⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ConditionalReplacement
