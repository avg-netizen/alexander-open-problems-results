import Alexander313.Wilken.SourceOneNativeSkContextFidelity
import Alexander313.Wilken.PublicEpsilonNativeSkIteration
import Alexander313.Wilken.HereditarySourceZetaTransport

/-!
# Original source-zero LOW provenance along every continuing sk path

The actual source-one first step provides the original HIGH representative
and real unrestricted next-mu value. Actual native Path induction repeats
the genuine contextual fidelity at continuing nodes. An emitted stop is
at most its current mu, so its canonical public value returns through the
original source-zero dictionary below the genuinely derived finiteBase1
bound. Every chronological entry therefore has a real original Normal LOW
code. No Native base-one parser, global endpoint or representative oracle.
The finite original-source return is explicit and primitive recursive;
these source-only candidates remain uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkSourcePathSupport

theorem root_acceptedLow (root : Nat) (ha : Mu.inputCheck root = true) :
    Theta.acceptedLowCode 0 root = true := by
  apply (Theta.acceptedLowCode_iff 0 root).mpr
  refine ⟨root_low root ha, ?_⟩
  obtain ⟨t, rfl, ht, hn, hh⟩ := (rootCheck_exact root).mp ha
  simpa only [ThetaCourse.rawTree_code] using hn

theorem mu_lt_public_boundary (root : Nat) (ha : Mu.inputCheck root = true) :
    Mu.sourceValue root < finiteBase 1 := by
  have he : Mu.muCode root ∈ Mu.execute root := (Mu.execute_graph root _).mpr ⟨ha, rfl⟩
  have hb := Mu.Bounds.execute_lt_public_endpoint root _ he
  rw [(Mu.muCode_spec root ha).2.2] at hb
  exact hb

def entryCode (q c : Nat) : Nat := SourceZeta.Transport.returnCode 0
  (NativeContext.UniformPublicReturn.publicCode q c)

theorem entryCode_primrec : Primrec₂ entryCode :=
  (SourceZeta.Transport.returnCode_primrec.comp (Primrec.const 0)
    NativeContext.UniformPublicReturn.publicCode_primrec).to₂

theorem entryCode_spec (q c : Nat) (hc : NativeContext.lowCheckCode q c = true)
    (hb : NativeContext.interpretation q c < finiteBase 1) :
    Theta.acceptedLowCode 0 (entryCode q c) = true ∧
      interpretation 0 (entryCode q c) = NativeContext.interpretation q c := by
  have hp := NativeContext.UniformPublicReturn.publicCode_spec q c
    ((NativeContext.UniformPublicReturn.inputCheck_exact q c).mpr hc)
  have hr := SourceZeta.Transport.returnCode_spec 0 _ hp.1 (hp.2.trans_lt hb)
  exact ⟨hr.1, hr.2.trans hp.2⟩

/-- Current source-one mu fidelity supplies the genuine original return
bound for every emitted stopping value, without assuming it is HIGH. -/
theorem stop_entry_spec (root q current c : Nat) (ha : Mu.inputCheck root = true)
    (hc : NativeContext.lowCheckCode (NativeContext.PublicEpsilonUnboundedIota.betaCode q current) c = true)
    (hm : Mu.sourceValue root = NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue q current)
    (hle : NativeContext.interpretation (NativeContext.PublicEpsilonUnboundedIota.betaCode q current) c ≤
      NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue q current) :
    Theta.acceptedLowCode 0 (entryCode (NativeContext.PublicEpsilonUnboundedIota.betaCode q current) c) = true ∧
      interpretation 0 (entryCode (NativeContext.PublicEpsilonUnboundedIota.betaCode q current) c) =
        NativeContext.interpretation (NativeContext.PublicEpsilonUnboundedIota.betaCode q current) c := by
  apply entryCode_spec _ c hc
  rw [← hm] at hle
  exact hle.trans_lt (mu_lt_public_boundary root ha)

/-- Actual Path induction retains original source-one current value/mu
fidelity at every continuation and derives original LOW codes for the
entire chronological word, including the final emitted stopping value. -/
theorem path_source_low {cutoff q current : Nat}
    {word : NativeContext.PublicEpsilonUnboundedIota.SkIteration.Support.Word}
    (hp : NativeContext.PublicEpsilonUnboundedIota.SkIteration.Path cutoff (q, current) word)
    (root : Nat) (ha : Mu.inputCheck root = true)
    (hv : interpretation 0 root = NativeContext.interpretation q current)
    (hm : Mu.sourceValue root = NativeContext.PublicEpsilonUnboundedIota.Mu.sourceValue q current) :
    ∀ entry ∈ word, ∃ d : Nat, Theta.acceptedLowCode 0 d = true ∧
      interpretation 0 d = NativeContext.interpretation entry.1 entry.2 := by
  induction hp generalizing root with
  | stop q current hc hcut hbound =>
    intro entry he
    rw [List.mem_singleton.mp he]
    exact ⟨root, root_acceptedLow root ha, hv⟩
  | nextStop q current out helig ho hh =>
    intro entry he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨root, root_acceptedLow root ha, hv⟩
    · rw [List.mem_singleton.mp he]
      have hs := NativeContext.PublicEpsilonUnboundedIota.SkNextSearch.execute_spec q current cutoff out ho
      exact ⟨entryCode (NativeContext.PublicEpsilonUnboundedIota.betaCode q current) out.2,
        stop_entry_spec root q current out.2 ha hs.2.1 hm
          (hs.2.2.2.1.le.trans
            (NativeContext.PublicEpsilonUnboundedIota.SkNextStep.nextValue_le_mu q current (unionInterpretation cutoff)))⟩
  | nextContinue q current out tail helig ho hh ht ih =>
    intro entry he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨root, root_acceptedLow root ha, hv⟩
    · have hs := SkContextFidelity.continued_source root q current cutoff out ha ho hh hv hm
      exact ih (SkContextFidelity.sourceRoot root out.2) hs.1 hs.2.1 hs.2.2.2.1 entry he

/-- The ORIGINAL executing first step and actual subsequent native loop
alone derive an original source-zero LOW witness for every native entry. -/
theorem first_loop_source_low (root cutoff : Nat) (out : SkNextSearch.Step)
    (ho : out ∈ SkNextSearch.execute (root, cutoff)) (hh : out.1 = true)
    (word : NativeContext.PublicEpsilonUnboundedIota.SkIteration.Support.Word)
    (hw : word ∈ NativeContext.PublicEpsilonUnboundedIota.SkIteration.execute
      ((alphaCode root, out.2), cutoff)) :
    ∀ entry ∈ word, ∃ d : Nat, Theta.acceptedLowCode 0 d = true ∧
      interpretation 0 d = NativeContext.interpretation entry.1 entry.2 := by
  have hs := SkContextFidelity.first_source root cutoff out ho hh
  have hp := (NativeContext.PublicEpsilonUnboundedIota.SkIteration.execute_spec _ _ _ word hw).2.1
  exact path_source_low hp (SkContextFidelity.sourceRoot root out.2) hs.1 hs.2.1 hs.2.2.2.1

theorem first_loop_entry_bound (root cutoff : Nat) (out : SkNextSearch.Step)
    (ho : out ∈ SkNextSearch.execute (root, cutoff)) (hh : out.1 = true)
    (word : NativeContext.PublicEpsilonUnboundedIota.SkIteration.Support.Word)
    (hw : word ∈ NativeContext.PublicEpsilonUnboundedIota.SkIteration.execute
      ((alphaCode root, out.2), cutoff)) (entry : NativeContext.PublicEpsilonUnboundedIota.Context)
    (he : entry ∈ word) : NativeContext.interpretation entry.1 entry.2 < finiteBase 1 := by
  obtain ⟨d, hd, hv⟩ := first_loop_source_low root cutoff out ho hh word hw entry he
  exact hv ▸ (lt_nextBase_iff_code 0 _).mpr ⟨d, ((Theta.acceptedLowCode_iff 0 d).mp hd).1, rfl⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SkSourcePathSupport
