import Alexander313.Wilken.HereditaryMuPublicDictionaryAgreement

/-!
# Actual public mu recurrence carried by the selected sk execution

The chronological public certificate uses the independently executing
canonical public mu query at every current epsilon. Original source-path
induction derives its input guard and numerical fidelity from genuine
original LOW bounds, retaining the exact overlined factor truncation and
both maximal stops. No cross-source mu or recurrence is supplied.
Uncompiled source candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicRecurrence

noncomputable def muValue (gamma : Nat) : Ordinal.{0} :=
  unionInterpretation (MuPublicDictionary.publicCode gamma)

inductive Path (cutoff : Nat) : List Nat → Prop
  | stop (a : Nat) (ha : MuPublicDictionary.Support.inputCheck a = true)
      (hb : muValue a < unionInterpretation cutoff) : Path cutoff [a]
  | nextStop (a d : Nat) (ha : MuPublicDictionary.Support.inputCheck a = true)
      (hd : Canonical.check d = true) (he : unionInterpretation cutoff ≤ muValue a)
      (hv : unionInterpretation d = MultiplicativeFactorTruncation.truncate (muValue a) (unionInterpretation cutoff))
      (hs : ¬(Ordinal.omega0 ^ unionInterpretation d = unionInterpretation d ∧
        unionInterpretation a < unionInterpretation d)) : Path cutoff [a, d]
  | nextContinue (a b : Nat) (xs : List Nat) (ha : MuPublicDictionary.Support.inputCheck a = true)
      (hb : MuPublicDictionary.Support.inputCheck b = true) (he : unionInterpretation cutoff ≤ muValue a)
      (hv : unionInterpretation b = MultiplicativeFactorTruncation.truncate (muValue a) (unionInterpretation cutoff))
      (hab : unionInterpretation a < unionInterpretation b)
      (ht : Path cutoff (b :: xs)) : Path cutoff (a :: b :: xs)

open MuPublicDictionary.Agreement

theorem native_path_low {q cutoff : Nat} {codes : List Nat}
    (hp : NativeContext.PublicEpsilonUnboundedIota.SkSourceRecurrence.SourcePath q cutoff codes) :
    ∀ d ∈ codes, NativeContext.lowCheckCode q d = true := by
  induction hp with
  | stop a ha hb =>
    intro d hd
    rw [List.mem_singleton.mp hd]
    exact ((NativeContext.SourceTrackingRaw.Support.inputCheck_exact q a).mp ha).1
  | nextStop a d ha hl he hv hs =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ((NativeContext.SourceTrackingRaw.Support.inputCheck_exact q a).mp ha).1
    · rw [List.mem_singleton.mp hc]; exact hl
  | nextContinue a b xs ha hb he hv hab ht ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ((NativeContext.SourceTrackingRaw.Support.inputCheck_exact q a).mp ha).1
    · exact ih d hd

theorem source_one_path_low {cutoff : Nat} {codes : List Nat}
    (hp : SourceOneIota.SkSourceRecurrence.SourcePath cutoff codes) :
    ∀ d ∈ codes, lowCheckCode 0 d = true := by
  induction hp with
  | stop a ha hb =>
    intro d hd
    rw [List.mem_singleton.mp hd]
    exact ((SourceOneIota.SourceTrackingRaw.Support.inputCheck_exact a).mp ha).1
  | nextStop a d ha hl he hv hs =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ((SourceOneIota.SourceTrackingRaw.Support.inputCheck_exact a).mp ha).1
    · rw [List.mem_singleton.mp hc]; exact hl
  | nextContinue a b xs ha hb he hv hab ht ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ((SourceOneIota.SourceTrackingRaw.Support.inputCheck_exact a).mp ha).1
    · exact ih d hd

/-- Every actual positive original-source current epsilon selects that
SAME source, so the independent public mu executes its actual recurrence. -/
theorem native_path (s cutoff : Nat) {codes : List Nat}
    (hp : NativeContext.PublicEpsilonUnboundedIota.SkSourceRecurrence.SourcePath
      (NativePublicBridge.contextCode s) cutoff codes) :
    Path cutoff (codes.map (positivePublicCode s)) := by
  induction hp with
  | stop a ha hb =>
    simpa only [List.map_cons, List.map_nil] using
      Path.stop (positivePublicCode s a) (positive_caller s a ha)
        (by rw [muValue, positive_public_mu s a ha]; exact hb)
  | nextStop a d ha hl he hv hs =>
    have hd := NativeContext.UniformPublicReturn.publicCode_spec _ d
      ((NativeContext.UniformPublicReturn.inputCheck_exact _ d).mpr hl)
    have had := NativeContext.UniformPublicReturn.publicCode_spec _ a
      ((NativeContext.UniformPublicReturn.inputCheck_exact _ a).mpr
        ((NativeContext.SourceTrackingRaw.Support.inputCheck_exact _ a).mp ha).1)
    simpa only [List.map_cons, List.map_nil] using
      Path.nextStop (positivePublicCode s a) (positivePublicCode s d) (positive_caller s a ha) hd.1
        (by rw [muValue, positive_public_mu s a ha]; exact he)
        (by rw [hd.2, muValue, positive_public_mu s a ha]; exact hv)
        (by simpa only [hd.2, had.2] using hs)
  | nextContinue a b xs ha hb he hv hab ht ih =>
    have hpa := NativeContext.UniformPublicReturn.publicCode_spec _ a
      ((NativeContext.UniformPublicReturn.inputCheck_exact _ a).mpr
        ((NativeContext.SourceTrackingRaw.Support.inputCheck_exact _ a).mp ha).1)
    have hpb := NativeContext.UniformPublicReturn.publicCode_spec _ b
      ((NativeContext.UniformPublicReturn.inputCheck_exact _ b).mpr
        ((NativeContext.SourceTrackingRaw.Support.inputCheck_exact _ b).mp hb).1)
    simpa only [List.map_cons] using
      Path.nextContinue (positivePublicCode s a) (positivePublicCode s b) (xs.map (positivePublicCode s))
        (positive_caller s a ha) (positive_caller s b hb)
        (by rw [muValue, positive_public_mu s a ha]; exact he)
        (by rw [hpb.2, muValue, positive_public_mu s a ha]; exact hv)
        (by rw [hpa.2, hpb.2]; exact hab) ih

theorem source_one_path (cutoff : Nat) {codes : List Nat}
    (hp : SourceOneIota.SkSourceRecurrence.SourcePath cutoff codes) :
    Path cutoff (codes.map sourceOnePublicCode) := by
  induction hp with
  | stop a ha hb =>
    simpa only [List.map_cons, List.map_nil] using
      Path.stop (sourceOnePublicCode a) (source_one_caller a ha)
        (by rw [muValue, source_one_public_mu a ha]; exact hb)
  | nextStop a d ha hl he hv hs =>
    have hd := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec d hl
    have had := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec a
      ((SourceOneIota.SourceTrackingRaw.Support.inputCheck_exact a).mp ha).1
    simpa only [List.map_cons, List.map_nil] using
      Path.nextStop (sourceOnePublicCode a) (sourceOnePublicCode d) (source_one_caller a ha) hd.1
        (by rw [muValue, source_one_public_mu a ha]; exact he)
        (by rw [hd.2, muValue, source_one_public_mu a ha]; exact hv)
        (by simpa only [hd.2, had.2] using hs)
  | nextContinue a b xs ha hb he hv hab ht ih =>
    have hpa := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec a
      ((SourceOneIota.SourceTrackingRaw.Support.inputCheck_exact a).mp ha).1
    have hpb := SourceOneIota.SourceTrackingRaw.Support.publicCode_spec b
      ((SourceOneIota.SourceTrackingRaw.Support.inputCheck_exact b).mp hb).1
    simpa only [List.map_cons] using
      Path.nextContinue (sourceOnePublicCode a) (sourceOnePublicCode b) (xs.map sourceOnePublicCode)
        (source_one_caller a ha) (source_one_caller b hb)
        (by rw [muValue, source_one_public_mu a ha]; exact he)
        (by rw [hpb.2, muValue, source_one_public_mu a ha]; exact hv)
        (by rw [hpa.2, hpb.2]; exact hab) ih

/-- The current value is the actual result of the independent public mu
execution, rather than an unspecified global operator. -/
theorem Path.head_mu {cutoff a : Nat} {xs : List Nat} (hp : Path cutoff (a :: xs)) :
    MuPublicDictionary.publicCode a ∈ MuPublicDictionary.execute a ∧
      Canonical.check (MuPublicDictionary.publicCode a) = true := by
  have ha : MuPublicDictionary.Support.inputCheck a = true := by
    cases hp <;> assumption
  exact ⟨MuPublicDictionary.execute_returns a ha, (MuPublicDictionary.publicCode_spec a ha).1⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SkPublicRecurrence
