import Alexander313.Wilken.HereditaryGlobalAdditiveTrackingExact
import Alexander313.Wilken.HereditaryPublicTrackingSequences

/-!
# Actual original reference words have independent public certificates

Every canonical emission retains its actual original source. The proved
same-source public mu agreement transports genuine adjacent covers, rather
than assuming a reference certificate from an assignment. These helpers
cover source zero and the positive finite native dictionaries. Uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking.RelativeCertificate

open NativeContext.SourceTrackingSequences (lastCode lastCode_append_singleton)
open Hereditary.FinePredecessor (stripLast stripLast_split)
open MuPublicDictionary.Agreement (positivePublicCode sourceOnePublicCode)

theorem stripLast_map (f : Nat → Nat) (xs : List Nat) :
    stripLast (xs.map f) = (stripLast xs).map f := by
  simp only [stripLast, List.map_reverse, List.map_tail]

theorem lastCode_map (f : Nat → Nat) (xs : List Nat) (hne : xs ≠ []) :
    lastCode (xs.map f) = f (lastCode xs) := by
  obtain ⟨last, he, hh⟩ := stripLast_split xs hne
  have hl : lastCode xs = last := by simp only [lastCode, hh, Option.getD_some]
  have hm : lastCode (xs.map f) = f last := by
    rw [he, List.map_append, List.map_cons, List.map_nil, lastCode_append_singleton]
  exact hm.trans (congrArg f hl.symm)

theorem source_one_reference {xs : List Nat}
    (hr : SourceOneIota.SourceTrackingRaw.Reference xs) :
    PublicTrackingSequences.Reference (xs.map sourceOnePublicCode) := by
  induction hr with
  | nil => exact .nil
  | one a ha => exact .one _ (MuPublicDictionary.Agreement.source_one_caller a ha)
  | cons a b xs ha hab hcover ht ih =>
    have hb := ht.nodes b List.mem_cons_self
    have hva := (SourceOneIota.SourceTrackingRaw.Support.publicCode_spec a
      ((SourceOneIota.SourceTrackingRaw.Support.inputCheck_exact a).mp ha).1).2
    have hvb := (SourceOneIota.SourceTrackingRaw.Support.publicCode_spec b
      ((SourceOneIota.SourceTrackingRaw.Support.inputCheck_exact b).mp hb).1).2
    refine .cons _ _ _ (MuPublicDictionary.Agreement.source_one_caller a ha) ?_ ?_ ih
    · simpa only [hva, hvb] using hab
    · simpa only [SkPublicRecurrence.muValue, hvb,
        MuPublicDictionary.Agreement.source_one_public_mu a ha] using hcover

theorem native_reference_tail (s a : Nat) (xs : List Nat)
    (hr : NativeContext.SourceTrackingRaw.Reference (NativePublicBridge.contextCode s) (a :: xs)) :
    NativeContext.SourceTrackingRaw.Reference (NativePublicBridge.contextCode s) xs := by
  refine ⟨fun c hc => hr.nodes c (List.mem_cons_of_mem _ hc), ?_⟩
  cases xs with
  | nil => exact .nil
  | cons b xs =>
    have ht := hr.2
    change NativeContext.SourceTrackingSequences.Reference (NativePublicBridge.contextCode s)
      (NativeContext.SourceTrackingRaw.Support.rootCode (NativePublicBridge.contextCode s) a ::
        NativeContext.SourceTrackingRaw.Support.rootCode (NativePublicBridge.contextCode s) b ::
          NativeContext.SourceTrackingRaw.Support.rootWord (NativePublicBridge.contextCode s) xs) at ht
    cases ht with
    | cons a b xs ha hab hcover ht => exact ht

theorem native_reference (s : Nat) (xs : List Nat)
    (hr : NativeContext.SourceTrackingRaw.Reference (NativePublicBridge.contextCode s) xs) :
    PublicTrackingSequences.Reference (xs.map (positivePublicCode s)) := by
  revert hr
  induction xs with
  | nil => intro hr; exact .nil
  | cons a xs ih =>
    intro hr
    have ha := hr.nodes a List.mem_cons_self
    cases xs with
    | nil => exact .one _ (MuPublicDictionary.Agreement.positive_caller s a ha)
    | cons b xs =>
      have hb := hr.nodes b (List.mem_cons_of_mem _ List.mem_cons_self)
      have hva := (NativeContext.UniformPublicReturn.publicCode_spec _ a
        ((NativeContext.UniformPublicReturn.inputCheck_exact _ a).mpr
          ((NativeContext.SourceTrackingRaw.Support.inputCheck_exact _ a).mp ha).1)).2
      have hvb := (NativeContext.UniformPublicReturn.publicCode_spec _ b
        ((NativeContext.UniformPublicReturn.inputCheck_exact _ b).mpr
          ((NativeContext.SourceTrackingRaw.Support.inputCheck_exact _ b).mp hb).1)).2
      have hab : NativeContext.interpretation (NativePublicBridge.contextCode s) a <
          NativeContext.interpretation (NativePublicBridge.contextCode s) b :=
        (List.pairwise_cons.mp (show
          (NativeContext.interpretation (NativePublicBridge.contextCode s) a ::
            (b :: xs).map (NativeContext.interpretation (NativePublicBridge.contextCode s))).Pairwise (· < ·)
          from by simpa only [List.map_cons] using hr.strict)).1 _ (List.mem_map.mpr ⟨b, List.mem_cons_self, rfl⟩)
      refine .cons _ _ _ (MuPublicDictionary.Agreement.positive_caller s a ha) ?_ ?_
        (ih (native_reference_tail s a (b :: xs) hr))
      · simpa only [SkPublicDictionary.PositiveAgreement.publicCode, hva, hvb] using hab
      · have hcover := hr.cover
        have hmu := MuPublicDictionary.Agreement.positive_public_mu s a ha
        rw [SkPublicRecurrence.muValue, hmu]
        simpa only [SkPublicDictionary.PositiveAgreement.publicCode, hvb] using hcover

end Alexander313.Wilken.RelativeTerm.Hereditary.GlobalAdditiveTracking.RelativeCertificate
