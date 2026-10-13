import Alexander313.Wilken.PublicEpsilonNativeAdditiveTrackingFrameOrderSupport
import Alexander313.Wilken.PublicEpsilonNativeMultiplicativeTrackingOrder

/-!
# Actual conditional replacements preserve strict factor order

Two raised executions use the SAME literal raised epsilon base, so genuine
multiplicative-word order and their returned VALUES compare the whole words.
Two small executions compare actual positive-left products. At the crossing,
the small product is at most head squared, strictly below every actual raised
multiplicative entry by true multiplicative closure. No cutoff, replacement
word or lexical comparison is assumed. Full insertion and non-M input order
remain separate. Source-only uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ConditionalOrderSupport

open PublicEpsilonUnboundedIota SourceTrackingSequences

/-- A real raised M word has genuine M entries, including its unchanged
factor and every HIGH epsilon in its actual written proper prefix. -/
theorem raised_word_member_multiplicative (q head factor : Nat) (word : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hlt : interpretation q head < interpretation q factor)
    (hw : word ∈ ReplacementSupport.raisedWord q head factor) :
    ∀ d ∈ word, MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal
      (interpretation (ReplacementSupport.raisedBaseCode q head) d) := by
  obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hw
  have hi := ReplacementSupport.raisedSearch_multiplicative q head factor c hh hf hm hlt hc
  have hs := ReplacementSupport.raisedSearch_spec q head factor c hh hf hc
  have hr := SourceMultiplicativePrincipal.rootInput _ c hi
  intro d hd
  rcases ReplacementSupport.rawWord_member _ c d hd with rfl | hprefix
  · simpa only [hs.2.2] using hm
  · exact SourceMultiplicativePrincipal.epsilon_multiplicative _
      (RootLowCollapse.root_epsilon _ d
        (SourceMultiplicativeTracking.properPrefix_roots _ _ hr d hprefix))

theorem raised_replacement_member_multiplicative (q head factor : Nat) (out : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hf : lowCheckCode q factor = true)
    (hm : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q factor))
    (hlt : interpretation q head < interpretation q factor)
    (ho : out ∈ Replacement.raisedReplacement q head factor) :
    ∀ d ∈ out, MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q d) := by
  obtain ⟨word, hw, ht, hv, hlen, hchecked⟩ :=
    Replacement.raisedReplacement_spec q head factor out hh hf hm hlt ho
  intro d hd
  have hmem : interpretation q d ∈ word.map
      (interpretation (ReplacementSupport.raisedBaseCode q head)) := by
    rw [← hv]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hmem
  rw [← he]
  exact raised_word_member_multiplicative q head factor word hh hf hm hlt hw a ha

/-- The two genuine raised searches use the same written base. Actual
M-word order there is preserved by the two independently executing returns. -/
theorem raised_replacements_lex (q head left right : Nat) (xs ys : List Nat)
    (hh : SourceTrackingRaw.Support.inputCheck q head = true)
    (hl : lowCheckCode q left = true) (hr : lowCheckCode q right = true)
    (hml : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q left))
    (hmr : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q right))
    (hhead : interpretation q head < interpretation q left)
    (hlt : interpretation q left < interpretation q right)
    (hx : xs ∈ Replacement.raisedReplacement q head left)
    (hy : ys ∈ Replacement.raisedReplacement q head right) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  obtain ⟨leftWord, hwx, htx, hvx, hlenx, hcx⟩ :=
    Replacement.raisedReplacement_spec q head left xs hh hl hml hhead hx
  obtain ⟨rightWord, hwy, hty, hvy, hleny, hcy⟩ :=
    Replacement.raisedReplacement_spec q head right ys hh hr hmr (hhead.trans hlt) hy
  obtain ⟨a, ha, hexa⟩ := (Part.mem_map_iff _).mp hwx
  obtain ⟨b, hb, heyb⟩ := (Part.mem_map_iff _).mp hwy
  have hia := ReplacementSupport.raisedSearch_multiplicative q head left a hh hl hml hhead ha
  have hib := ReplacementSupport.raisedSearch_multiplicative q head right b hh hr hmr
    (hhead.trans hlt) hb
  have hsa := ReplacementSupport.raisedSearch_spec q head left a hh hl ha
  have hsb := ReplacementSupport.raisedSearch_spec q head right b hh hr hb
  rw [hvx, hvy, ← hexa, ← heyb]
  exact SourceMultiplicativeTracking.Order.rawWord_multiplicative_lex _ a b hia hib
    (by rw [hsa.2.2, hsb.2.2]; exact hlt)

/-- The actual conditional procedure at one written head is strictly
lexicographically increasing in its genuine M factor. The original joint
callers derive both executions and all raised comparisons. -/
theorem conditional_replacements_lex (q : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true) (head left right : Nat)
    (hhead : head ∈ heads)
    (hl : lowCheckCode q left = true) (hr : lowCheckCode q right = true)
    (hml : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q left))
    (hmr : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q right))
    (hbl : interpretation q left ≤ interpretation q (lastCode heads))
    (hbr : interpretation q right ≤ interpretation q (lastCode heads))
    (hlt : interpretation q left < interpretation q right)
    (xs ys : List Nat) (hx : xs ∈ ConditionalReplacement.execute q head left)
    (hy : ys ∈ ConditionalReplacement.execute q head right) :
    List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q)) := by
  have hsx := ConditionalReplacement.execute_spec q heads hh head left hhead hl hml hbl xs hx
  have hsy := ConditionalReplacement.execute_spec q heads hh head right hhead hr hmr hbr ys hy
  rcases hsx.2.2 with hraisedx | ⟨hsmallx, a, hexa, hva⟩
  · rcases hsy.2.2 with hraisedy | ⟨hsmally, b, heyb, hvb⟩
    · exact raised_replacements_lex q head left right xs ys
        (ConditionalReplacement.raised_member_caller q heads hh head left hhead hraisedx.1 hbl).2
        hl hr hml hmr hraisedx.1 hlt hraisedx.2.1 hraisedy.2.1
    · exact False.elim ((hraisedx.1.trans hlt).not_ge hsmally)
  · rcases hsy.2.2 with hraisedy | ⟨hsmally, b, heyb, hvb⟩
    · have hraw := (ConditionalReplacement.raised_member_caller q heads hh head right
        hhead hraisedy.1 hbr).2
      have hstrict := FrameOrderSupport.raised_replacement_member_gt_head q head right ys
        hraw hr hmr hraisedy.1 hraisedy.2.1
      have hmember := raised_replacement_member_multiplicative q head right ys
        hraw hr hmr hraisedy.1 hraisedy.2.1
      rw [hexa, List.map_singleton]
      cases he : ys with
      | nil => exact False.elim (hsy.1 he)
      | cons b bs =>
        have hbmem : b ∈ ys := by simp only [he]; exact List.mem_cons_self
        have hhb := hstrict b hbmem
        have hsquare := (hmember b hbmem).2.2 hhb hhb
        have hap : interpretation q a ≤ interpretation q head * interpretation q head := by
          rw [hva]
          exact mul_le_mul_right hsmallx _
        simp only [he, List.map_cons]
        exact List.Lex.rel (hap.trans_lt hsquare)
    · rw [hexa, heyb]
      simp only [List.map_singleton]
      exact List.Lex.rel (by rw [hva, hvb]; exact mul_lt_mul_of_pos_left hlt
        (ConditionalReplacement.tracking_member_principal q heads hh head hhead).2.1)

/-- Strict lexicographic order between nonempty words implies a weak
comparison of their actual first values. -/
theorem lex_first_le (q : Nat) (xs ys : List Nat) (hx : xs ≠ []) (hy : ys ≠ [])
    (hlex : List.Lex (· < ·) (xs.map (interpretation q)) (ys.map (interpretation q))) :
    interpretation q (Insertion.firstCode xs) ≤ interpretation q (Insertion.firstCode ys) := by
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons a as =>
    cases ys with
    | nil => exact False.elim (hy rfl)
    | cons b bs =>
      simp only [Insertion.firstCode, List.head?_cons, Option.getD_some]
      simp only [List.map_cons] at hlex
      exact List.head_le_of_lt hlex

/-- A genuine cover of the larger-factor replacement FIRST is also a
cover of the smaller-factor replacement FIRST at the SAME written head. -/
theorem cover_smaller_replacement (q : Nat) (heads : List Nat)
    (hh : SourceTrackingRaw.trackingCheck q heads = true) (head left right previous : Nat)
    (hhead : head ∈ heads)
    (hl : lowCheckCode q left = true) (hr : lowCheckCode q right = true)
    (hml : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q left))
    (hmr : MultiplicativePrincipalArithmetic.IsMultiplicativePrincipal (interpretation q right))
    (hbl : interpretation q left ≤ interpretation q (lastCode heads))
    (hbr : interpretation q right ≤ interpretation q (lastCode heads))
    (hlt : interpretation q left < interpretation q right)
    (xs ys : List Nat) (hx : xs ∈ ConditionalReplacement.execute q head left)
    (hy : ys ∈ ConditionalReplacement.execute q head right)
    (hcover : Insertion.coverCheck q previous (Insertion.firstCode ys) = true) :
    Insertion.coverCheck q previous (Insertion.firstCode xs) = true := by
  have hsx := ConditionalReplacement.execute_spec q heads hh head left hhead hl hml hbl xs hx
  have hsy := ConditionalReplacement.execute_spec q heads hh head right hhead hr hmr hbr ys hy
  have hfirst := lex_first_le q xs ys hsx.1 hsy.1
    (conditional_replacements_lex q heads hh head left right hhead hl hr hml hmr hbl hbr hlt xs ys hx hy)
  have hmem : Insertion.firstCode xs ∈ xs := by
    cases he : xs with
    | nil => exact False.elim (hsx.1 he)
    | cons a as =>
      simp only [Insertion.firstCode, he, List.head?_cons, Option.getD_some]
      exact List.mem_cons_self
  have hc := (Insertion.coverCheck_exact q previous (Insertion.firstCode ys)).mp hcover
  exact (Insertion.coverCheck_exact q previous (Insertion.firstCode xs)).mpr
    ⟨hc.1, (hsx.2.1 _ hmem).1, hfirst.trans hc.2.2⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceAdditiveTracking.ConditionalOrderSupport
