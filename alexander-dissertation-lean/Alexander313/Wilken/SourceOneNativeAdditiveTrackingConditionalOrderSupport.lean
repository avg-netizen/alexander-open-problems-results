import Alexander313.Wilken.SourceOneNativeAdditiveTrackingFrameOrderSupport
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingOrder

/-!
# Strict factor order of actual original source-one replacements

Both raised executions use the same actual coded epsilon head and genuine
native multiplicative words. Their independently executed original-zero
returns preserve the full value lists. Both small executions use real
positive-left products. At the crossing the smaller product is at most
head squared, strictly below every real raised M entry by multiplicative
closure. Original check zero is retained; there is no Native base-one
parser or supplied replacement comparison. Full insertion and non-M input
order remain separate. Source-only and uncompiled.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ConditionalOrderSupport

open NativeContext.SourceTrackingSequences (lastCode)

/-- The actual searched final factor and every actual HIGH proper entry
are genuine multiplicative principals at the real raised epsilon base. -/
theorem raised_word_member_multiplicative (head factor : Nat) (word : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hlt : interpretation 0 head < interpretation 0 factor)
    (hw : word ∈ ReplacementSupport.raisedWord head factor) :
    ∀ d ∈ word, MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) d) := by
  obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hw
  have hi := ReplacementSupport.raisedSearch_multiplicative head factor c hh hf hm hlt hc
  have hs := ReplacementSupport.raisedSearch_spec head factor c hf hc
  have hr := NativeContext.SourceMultiplicativePrincipal.rootInput _ c hi
  intro d hd
  rcases NativeContext.SourceAdditiveTracking.ReplacementSupport.rawWord_member _ c d hd with
    rfl | hprefix
  · simpa only [hs.2.2] using hm
  · exact NativeContext.SourceMultiplicativePrincipal.epsilon_multiplicative _
      (NativeContext.RootLowCollapse.root_epsilon _ d
        (NativeContext.SourceMultiplicativeTracking.properPrefix_roots _ _ hr d hprefix))

/-- Every member of the actual raised word is strictly above its genuine
base head, including the independently searched literal final factor. -/
theorem raised_word_member_gt_head (head factor : Nat) (word : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hlt : interpretation 0 head < interpretation 0 factor)
    (hw : word ∈ ReplacementSupport.raisedWord head factor) :
    ∀ d ∈ word, interpretation 0 head <
      NativeContext.interpretation (ReplacementSupport.raisedBaseCode head) d := by
  obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hw
  have hi := ReplacementSupport.raisedSearch_multiplicative head factor c hh hf hm hlt hc
  have hs := ReplacementSupport.raisedSearch_spec head factor c hf hc
  have hr := NativeContext.SourceMultiplicativePrincipal.rootInput _ c hi
  have hb := (ReplacementSupport.raisedBaseCode_spec head hh).2.1
  intro d hd
  rcases NativeContext.SourceAdditiveTracking.ReplacementSupport.rawWord_member _ c d hd with
    rfl | hprefix
  · rw [hs.2.2]
    exact hlt
  · have hhigh := NativeContext.SourceMultiplicativeTracking.properPrefix_roots _ _ hr d hprefix
    simpa only [hb] using NativeContext.PublicEpsilonUnboundedIota.Mu.root_base_lt _ d hhigh

/-- Actual original-zero returns preserve each genuine raised M value;
the returned spelling need not be the raised spelling. -/
theorem raised_replacement_member_multiplicative (head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hlt : interpretation 0 head < interpretation 0 factor)
    (ho : out ∈ Replacement.raisedReplacement head factor) :
    ∀ d ∈ out, MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 d) := by
  obtain ⟨word, hw, he, ht, hv, hlen, hchecked⟩ :=
    Replacement.raisedReplacement_spec head factor out hh hf hm hlt ho
  intro d hd
  have hmem : interpretation 0 d ∈ word.map
      (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head)) := by
    rw [← hv]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hmem
  rw [← he]
  exact raised_word_member_multiplicative head factor word hh hf hm hlt hw a ha

theorem raised_replacement_member_gt_head (head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hf : lowCheckCode 0 factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 factor))
    (hlt : interpretation 0 head < interpretation 0 factor)
    (ho : out ∈ Replacement.raisedReplacement head factor) :
    ∀ d ∈ out, interpretation 0 head < interpretation 0 d := by
  obtain ⟨word, hw, he, ht, hv, hlen, hchecked⟩ :=
    Replacement.raisedReplacement_spec head factor out hh hf hm hlt ho
  intro d hd
  have hmem : interpretation 0 d ∈ word.map
      (NativeContext.interpretation (ReplacementSupport.raisedBaseCode head)) := by
    rw [← hv]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hmem
  rw [← he]
  exact raised_word_member_gt_head head factor word hh hf hm hlt hw a ha

/-- Independent raised searches at the same literal coded head give
strictly ordered M words, preserved by both actual original returns. -/
theorem raised_replacements_lex (head left right : Nat) (xs ys : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck head = true)
    (hl : lowCheckCode 0 left = true) (hr : lowCheckCode 0 right = true)
    (hml : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 left))
    (hmr : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 right))
    (hhead : interpretation 0 head < interpretation 0 left)
    (hlt : interpretation 0 left < interpretation 0 right)
    (hx : xs ∈ Replacement.raisedReplacement head left)
    (hy : ys ∈ Replacement.raisedReplacement head right) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  obtain ⟨leftWord, hwx, hex, htx, hvx, hlenx, hcx⟩ :=
    Replacement.raisedReplacement_spec head left xs hh hl hml hhead hx
  obtain ⟨rightWord, hwy, hey, hty, hvy, hleny, hcy⟩ :=
    Replacement.raisedReplacement_spec head right ys hh hr hmr (hhead.trans hlt) hy
  obtain ⟨a, ha, hexa⟩ := (Part.mem_map_iff _).mp hwx
  obtain ⟨b, hb, heyb⟩ := (Part.mem_map_iff _).mp hwy
  have hia := ReplacementSupport.raisedSearch_multiplicative head left a hh hl hml hhead ha
  have hib := ReplacementSupport.raisedSearch_multiplicative head right b hh hr hmr
    (hhead.trans hlt) hb
  have hsa := ReplacementSupport.raisedSearch_spec head left a hl ha
  have hsb := ReplacementSupport.raisedSearch_spec head right b hr hb
  rw [hvx, hvy, ← hexa, ← heyb]
  exact NativeContext.SourceMultiplicativeTracking.Order.rawWord_multiplicative_lex _ a b hia hib
    (by rw [hsa.2.2, hsb.2.2]; exact hlt)

/-- The real conditional replacement at one unchanged original head is
strictly increasing in its M factor. All raised callers are derived from
the actual original tracking word and honest joint final bounds. -/
theorem conditional_replacements_lex (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) (head left right : Nat)
    (hhead : head ∈ heads)
    (hl : lowCheckCode 0 left = true) (hr : lowCheckCode 0 right = true)
    (hml : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 left))
    (hmr : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 right))
    (hbl : interpretation 0 left ≤ interpretation 0 (lastCode heads))
    (hbr : interpretation 0 right ≤ interpretation 0 (lastCode heads))
    (hlt : interpretation 0 left < interpretation 0 right)
    (xs ys : List Nat) (hx : xs ∈ ConditionalReplacement.execute head left)
    (hy : ys ∈ ConditionalReplacement.execute head right) :
    List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0)) := by
  have hsx := ConditionalReplacement.execute_spec heads hh head left hhead hl hml hbl xs hx
  have hsy := ConditionalReplacement.execute_spec heads hh head right hhead hr hmr hbr ys hy
  rcases hsx.2.2.2.2 with hraisedx | ⟨hsmallx, a, hexa, hva⟩
  · rcases hsy.2.2.2.2 with hraisedy | ⟨hsmally, b, heyb, hvb⟩
    · exact raised_replacements_lex head left right xs ys
        (ConditionalReplacement.raised_member_caller heads hh head left hhead hraisedx.1 hbl).2
        hl hr hml hmr hraisedx.1 hlt hraisedx.2 hraisedy.2
    · exact False.elim ((hraisedx.1.trans hlt).not_ge hsmally)
  · rcases hsy.2.2.2.2 with hraisedy | ⟨hsmally, b, heyb, hvb⟩
    · have hraw := (ConditionalReplacement.raised_member_caller heads hh head right
        hhead hraisedy.1 hbr).2
      have hstrict := raised_replacement_member_gt_head head right ys hraw hr hmr hraisedy.1 hraisedy.2
      have hmember := raised_replacement_member_multiplicative head right ys
        hraw hr hmr hraisedy.1 hraisedy.2
      rw [hexa, List.map_singleton]
      cases he : ys with
      | nil => exact False.elim (hsy.1 he)
      | cons b bs =>
        have hbmem : b ∈ ys := by simpa only [he] using (List.mem_cons_self : b ∈ b :: bs)
        have hhb := hstrict b hbmem
        have hsquare := (hmember b hbmem).2.2 hhb hhb
        have hap : interpretation 0 a ≤ interpretation 0 head * interpretation 0 head := by
          rw [hva]
          exact mul_le_mul_right hsmallx _
        simp only [he, List.map_cons]
        exact List.Lex.rel (hap.trans_lt hsquare)
    · rw [hexa, heyb]
      simp only [List.map_singleton]
      exact List.Lex.rel (by rw [hva, hvb]; exact mul_lt_mul_of_pos_left hlt
        (ConditionalReplacement.tracking_member_principal heads hh head hhead).2.1)

theorem lex_first_le (xs ys : List Nat) (hx : xs ≠ []) (hy : ys ≠ [])
    (hlex : List.Lex (· < ·) (xs.map (interpretation 0)) (ys.map (interpretation 0))) :
    interpretation 0 (Insertion.firstCode xs) ≤ interpretation 0 (Insertion.firstCode ys) := by
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons a as =>
    cases ys with
    | nil => exact False.elim (hy rfl)
    | cons b bs =>
      simp only [Insertion.firstCode, List.head?_cons, Option.getD_some]
      simp only [List.map_cons] at hlex
      exact List.head_le_of_lt hlex

/-- Covering the larger-factor result FIRST genuinely covers the
smaller-factor result FIRST, with both original LOW callers derived. -/
theorem cover_smaller_replacement (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck heads = true) (head left right previous : Nat)
    (hhead : head ∈ heads)
    (hl : lowCheckCode 0 left = true) (hr : lowCheckCode 0 right = true)
    (hml : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 left))
    (hmr : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation 0 right))
    (hbl : interpretation 0 left ≤ interpretation 0 (lastCode heads))
    (hbr : interpretation 0 right ≤ interpretation 0 (lastCode heads))
    (hlt : interpretation 0 left < interpretation 0 right)
    (xs ys : List Nat) (hx : xs ∈ ConditionalReplacement.execute head left)
    (hy : ys ∈ ConditionalReplacement.execute head right)
    (hcover : Insertion.coverCheck previous (Insertion.firstCode ys) = true) :
    Insertion.coverCheck previous (Insertion.firstCode xs) = true := by
  have hsx := ConditionalReplacement.execute_spec heads hh head left hhead hl hml hbl xs hx
  have hsy := ConditionalReplacement.execute_spec heads hh head right hhead hr hmr hbr ys hy
  have hfirst := lex_first_le xs ys hsx.1 hsy.1
    (conditional_replacements_lex heads hh head left right hhead hl hr hml hmr hbl hbr hlt xs ys hx hy)
  have hmem : Insertion.firstCode xs ∈ xs := by
    cases he : xs with
    | nil => exact False.elim (hsx.1 he)
    | cons a as =>
      simp only [Insertion.firstCode, he, List.head?_cons, Option.getD_some]
      exact List.mem_cons_self
  have hc := (Insertion.coverCheck_exact previous (Insertion.firstCode ys)).mp hcover
  exact (Insertion.coverCheck_exact previous (Insertion.firstCode xs)).mpr
    ⟨hc.1, ((Theta.acceptedLowCode_iff 0 _).mp (hsx.2.1 _ hmem)).1, hfirst.trans hc.2.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceAdditiveTracking.ConditionalOrderSupport
