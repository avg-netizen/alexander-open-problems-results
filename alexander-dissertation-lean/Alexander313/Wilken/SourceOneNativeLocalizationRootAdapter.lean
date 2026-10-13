import Alexander313.Wilken.SourceOneNativeTrackingRawSupport
import Alexander313.Wilken.HereditaryLocalizationRefinements

/-!
# Genuine original source-one raw principal localization callers

The original check-zero normalizer and final ANF atom produce a checked
Normal theta-zero Node with the original raw value. The full domain is
RAW LOW positive additive principals, including one and non-epsilon roots.
Parameter admission and the genuine LOW sort exclude every other shape.
HIGH is derived separately on the strict epsilon subcase. No Native
base-one parser, representation or endpoint oracle is supplied.
Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceLocalization.RootAdapter

open ThetaCourse

abbrev rootCode := SourceTrackingRaw.Support.rootCode

theorem rootCode_primrec : Primrec rootCode := SourceTrackingRaw.Support.rootCode_primrec

abbrev inputCheck := SourceTrackingRaw.Support.principalCheck

theorem inputCheck_primrec : Primrec inputCheck := SourceTrackingRaw.Support.principalCheck_primrec

/-- Positivity is exactly being at least the literal source-one base. -/
theorem inputCheck_exact (c : Nat) : inputCheck c = true ↔
    lowCheckCode 0 c = true ∧ 1 ≤ interpretation 0 c ∧
      Ordinal.IsPrincipal (· + ·) (interpretation 0 c) := by
  rw [SourceTrackingRaw.Support.principalCheck_exact]
  constructor
  · rintro ⟨hc, hp, ha⟩
    exact ⟨hc, Order.one_le_iff_pos.mpr hp, ha⟩
  · rintro ⟨hc, hp, ha⟩
    exact ⟨hc, Order.one_le_iff_pos.mp hp, ha⟩

/-- The complete original ANF supplies the actual root, including the
base-one boundary and non-epsilon final principals. -/
theorem rootCode_spec (c : Nat) (hi : inputCheck c = true) :
    Localization.Node 0 (rootCode c) ∧ interpretation 0 (rootCode c) = interpretation 0 c := by
  have hc := (SourceTrackingRaw.Support.principalCheck_exact c).mp hi
  let n := Theta.Normalization.normalizeCode 0 c
  have hn := Theta.Normalization.normalizeCode_acceptedLow 0 c hc.1
  have hl := (Theta.acceptedLowCode_iff 0 n).mp hn.1
  have hni : SourceDecomposition.inputCheck 0 n = true :=
    (SourceDecomposition.inputCheck_exact 0 n).mpr
      ⟨SourceTrackingRaw.Support.original_checked n hl.1, hl.2⟩
  have hw := SourceDecomposition.word_spec 0 n hni
  have hmap : (SourceDecomposition.word 0 n).map (denote 0) = [interpretation 0 c] := by
    rw [hw.2, hn.2, canonicalANF_principal hc.2.1 hc.2.2]
  have hlen : (SourceDecomposition.word 0 n).length = 1 := by
    simpa only [List.length_map, List.length_singleton] using congrArg List.length hmap
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.mp hlen
  have hm : t ∈ SourceDecomposition.word 0 n := by rw [ht]; exact List.mem_singleton_self _
  have hs := hw.1 t hm
  have hv : denote 0 t = interpretation 0 c := by
    simpa only [ht, List.map_singleton, List.singleton_inj] using hmap
  have hatom : LogEndZero.publicEndAtom 0 n = t := by
    simp only [LogEndZero.publicEndAtom, ht, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.getElem?_cons_zero, Option.getD_some]
  have hr : rootCode c = t.code := congrArg RelativeTerm.code hatom
  have hout : t.outerSort ≤ 1 := (denote_lt_iff_outerSort_le 0 t hs.1 1 (by omega)).mp (by
    rw [hv]
    exact (SourceTrackingRaw.Support.original_bound c hc.1).trans (finiteBase_lt_cardinal 0))
  rcases SourceDecomposition.word_shape 0 n t hm with ⟨p, rfl⟩ | ⟨k, a, rfl⟩
  · have hb := SourceFixedPoint.checked_parameter_lt_base 0 p hs.1
    rw [hv, finiteBase_zero] at hb
    exact False.elim ((Order.one_le_iff_pos.mpr hc.2.1).not_gt hb)
  · have hk : k = 0 := by simp only [RelativeTerm.outerSort] at hout; omega
    subst k
    exact ⟨⟨a, hr, hs.1, hs.2.1⟩, by rw [hr, interpretation_code, hv]⟩

theorem rootInput (c : Nat) (hi : inputCheck c = true) :
    Localization.inputCheck 0 (rootCode c) = true :=
  (Localization.inputCheck_exact 0 _).mpr (rootCode_spec c hi).1

theorem rootCode_value (c : Nat) (hi : inputCheck c = true) :
    interpretation 0 (rootCode c) = interpretation 0 c := (rootCode_spec c hi).2

theorem localization_endpoint_value (c : Nat) (hi : inputCheck c = true) :
    Localization.value 0 (Localization.endpoint (Localization.nativePath 0 (rootCode c))) =
      interpretation 0 c :=
  (Localization.nativePath_end 0 _ (rootInput c hi)).trans (rootCode_value c hi)

/-- HIGH is a separate derived property of the actual strict epsilon
subdomain; the full final-node adapter does not assume it. -/
theorem rootCode_high (c : Nat) (hi : inputCheck c = true)
    (hp : 1 < interpretation 0 c)
    (he : Ordinal.omega0 ^ interpretation 0 c = interpretation 0 c) :
    rootCheck (rootCode c) = true :=
  (SourceTrackingRaw.Support.rootCode_high c ((inputCheck_exact c).mp hi).1 hp he).1

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceLocalization.RootAdapter
