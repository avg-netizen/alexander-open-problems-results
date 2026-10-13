import Alexander313.Wilken.SourceOneNativeSkSourceValueInvariance

/-!
# Genuine original source-one raw initialization

The actual original source-zero RAW epsilon checker constructs the real
Normal HIGH root. Replacing only the first written code by an equal RAW
epsilon preserves the full recurrence and tracker through the proved
original raw mu value invariance. No Native base-one parser, written root
identity, endpoint, tracking or recurrence oracle. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkRaw.Support

open SkSourceRecurrence (SourcePath)
open SkTracking.Support (lastCode_cons_nonempty stripLast_cons_nonempty singleton_tracking)
open Hereditary.FinePredecessor (stripLast)
open NativeContext.SourceTrackingSequences (lastCode lastCode_singleton)

abbrev Query := SkSourceWord.Support.Query

def inputCheck (raw cutoff : Nat) : Bool :=
  SourceTrackingRaw.Support.inputCheck raw && unionCheck cutoff

theorem inputCheck_primrec : Primrec₂ inputCheck :=
  (Primrec.and.comp (SourceTrackingRaw.Support.inputCheck_primrec.comp Primrec.fst)
    (Uniform.unionCheck_primrec.comp Primrec.snd)).to₂

theorem inputCheck_exact (raw cutoff : Nat) : inputCheck raw cutoff = true ↔
    lowCheckCode 0 raw = true ∧ 1 < interpretation 0 raw ∧
      Ordinal.omega0 ^ interpretation 0 raw = interpretation 0 raw ∧
        unionCheck cutoff = true := by
  rw [inputCheck, Bool.and_eq_true, SourceTrackingRaw.Support.inputCheck_exact]
  exact ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩,
    fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩

def rootQuery (p : Query) : Query :=
  (SourceTrackingRaw.Support.rootCode p.1, p.2)

theorem rootQuery_primrec : Primrec rootQuery :=
  (SourceTrackingRaw.Support.rootCode_primrec.comp Primrec.fst).pair Primrec.snd

theorem root_caller (raw cutoff : Nat) (hi : inputCheck raw cutoff = true) :
    SkSourceWord.inputCheck (SourceTrackingRaw.Support.rootCode raw) cutoff = true := by
  obtain ⟨hr, hc⟩ := Bool.and_eq_true.mp hi
  exact (SkSourceWord.inputCheck_exact _ _).mpr
    ⟨(SourceTrackingRaw.Support.rootCode_spec raw hr).2.1, hc⟩

def restore (raw : Nat) (codes : List Nat) : List Nat := raw :: codes.tail

theorem restore_primrec : Primrec₂ restore :=
  (Primrec.list_cons.comp Primrec.fst (Primrec.list_tail.comp Primrec.snd)).to₂

theorem restore_cons (raw root : Nat) (tail : List Nat) :
    restore raw (root :: tail) = raw :: tail := rfl

/-- SAME original raw mu, actual truncation and strict epsilon tests
preserve both maximal stopping alternatives when only the head is changed. -/
theorem sourcePath_replace_head (cutoff raw root : Nat) (xs : List Nat)
    (hp : SourcePath cutoff (root :: xs))
    (hr : SourceTrackingRaw.Support.inputCheck raw = true)
    (hv : interpretation 0 raw = interpretation 0 root) :
    SourcePath cutoff (raw :: xs) := by
  cases hp with
  | stop root ha hb =>
    have hm := SourceTrackingRaw.Support.muValue_invariant raw root hr ha hv
    exact .stop raw hr (by rw [hm]; exact hb)
  | nextStop root d ha hl he hd hs =>
    have hm := SourceTrackingRaw.Support.muValue_invariant raw root hr ha hv
    exact .nextStop raw d hr hl (by rw [hm]; exact he)
      (by rw [hm]; exact hd) (by rw [hv]; exact hs)
  | nextContinue root d xs ha hd he hvalue hab ht =>
    have hm := SourceTrackingRaw.Support.muValue_invariant raw root hr ha hv
    exact .nextContinue raw d xs hr hd (by rw [hm]; exact he)
      (by rw [hm]; exact hvalue) (by rw [hv]; exact hab) ht

theorem reference_replace_head (raw root : Nat) (xs : List Nat)
    (hp : SourceTrackingRaw.Reference (root :: xs))
    (hr : SourceTrackingRaw.Support.inputCheck raw = true)
    (hv : interpretation 0 raw = interpretation 0 root) :
    SourceTrackingRaw.Reference (raw :: xs) := by
  cases hp with
  | one root ha => exact .one raw hr
  | cons root d xs ha hab hc ht =>
    have hm := SourceTrackingRaw.Support.muValue_invariant raw root hr ha hv
    exact .cons raw d xs hr (by rw [hv]; exact hab) (by rw [hm]; exact hc) ht

theorem last_mu_replace_head (raw root : Nat) (xs : List Nat)
    (hr : SourceTrackingRaw.Support.inputCheck raw = true)
    (ha : SourceTrackingRaw.Support.inputCheck root = true)
    (hv : interpretation 0 raw = interpretation 0 root) :
    SourceTrackingRaw.Support.muValue (lastCode (raw :: xs)) =
      SourceTrackingRaw.Support.muValue (lastCode (root :: xs)) := by
  cases xs with
  | nil =>
    simpa only [lastCode_singleton] using
      SourceTrackingRaw.Support.muValue_invariant raw root hr ha hv
  | cons d ds =>
    rw [lastCode_cons_nonempty raw _ (List.cons_ne_nil _ _),
      lastCode_cons_nonempty root _ (List.cons_ne_nil _ _)]

/-- The actual RAW tracker survives the literal first-code restoration;
all later written entries are unchanged. -/
theorem tracking_replace_head (raw root : Nat) (xs : List Nat)
    (ht : SourceTrackingRaw.trackingCheck (root :: xs) = true)
    (hr : SourceTrackingRaw.Support.inputCheck raw = true)
    (ha : SourceTrackingRaw.Support.inputCheck root = true)
    (hv : interpretation 0 raw = interpretation 0 root) :
    SourceTrackingRaw.trackingCheck (raw :: xs) = true := by
  cases xs with
  | nil =>
    have hs := (SourceTrackingRaw.Support.inputCheck_exact raw).mp hr
    have hp := EpsilonOffsets.epsilon_pos_principal hs.2.2
    exact singleton_tracking raw hs.1 hp.1 hp.2 hs.2.1.le
  | cons d ds =>
    have hs := (SourceTrackingRaw.trackingCheck_exact (root :: d :: ds)).mp ht
    have hne : d :: ds ≠ [] := List.cons_ne_nil _ _
    have hprefixRoot := stripLast_cons_nonempty root (d :: ds) hne
    have hprefixRaw := stripLast_cons_nonempty raw (d :: ds) hne
    have hlastRoot := lastCode_cons_nonempty root (d :: ds) hne
    have hlastRaw := lastCode_cons_nonempty raw (d :: ds) hne
    apply (SourceTrackingRaw.trackingCheck_exact _).mpr
    refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hprefixRaw]
      exact reference_replace_head raw root _ (by rw [← hprefixRoot]; exact hs.2.1) hr hv
    · rw [hlastRaw, ← hlastRoot]; exact hs.2.2.1
    · rw [hlastRaw, ← hlastRoot]; exact hs.2.2.2.1
    · rw [hlastRaw, ← hlastRoot]; exact hs.2.2.2.2.1
    · have hf := hs.2.2.2.2.2
      rw [hprefixRoot, if_neg (List.cons_ne_nil _ _), hlastRoot] at hf
      rw [hprefixRaw, if_neg (List.cons_ne_nil _ _), hlastRaw,
        last_mu_replace_head raw root _ hr ha hv]
      exact hf

theorem restore_values (raw root : Nat) (xs : List Nat)
    (hv : interpretation 0 raw = interpretation 0 root) :
    (restore raw (root :: xs)).map (interpretation 0) =
      (root :: xs).map (interpretation 0) := by
  simp only [restore_cons, List.map_cons, hv]

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkRaw.Support
