import Alexander313.Wilken.PublicEpsilonNativeLocalization
import Alexander313.Wilken.PublicEpsilonNativePowerBaseChangeSupport

/-!
# Literal ordinary localization under genuine original parameter transport

Every comparator caller below is an original admitted Node at both sources.
The actual same finite support, greatest-argument selector and live-list walk
therefore agree literally. The public caller is derived from the ORIGINAL
chosen parameter bound, rather than supplied target admission. No ordinal
value equality is used to infer a payload cutoff. Uncompiled source drafts.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization.BaseChange

open ThetaCourse

theorem node_checked (q c : Nat) (hc : Node q c) : checkCode q c = true :=
  ((Comparison.acceptedCode_exact q c).mp (node_accepted q c hc)).1

theorem node_change (q v c : Nat) (hc : Node q c) (hv : baseCheck v = true)
    (hp : BaseTransformation.ParBounded q v (rawTree c)) : Node v c := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  have hpayload : Payloads v (.theta 0 a) :=
    (BaseTransformation.parBounded_iff_payloads q v _ ha hv).mp
      (by simpa only [rawTree_code] using hp)
  have ht := BaseTransformation.check_change q v (.theta 0 a) ha hv hpayload
  have haq := FixedPoint.checked_theta_argument q 0 a ha
  have hav := FixedPoint.checked_theta_argument v 0 a ht
  exact ⟨a, rfl, ht, (BaseTransformation.normal_context q v a haq hav).mp hn⟩

theorem inputCheck_context (q v c : Nat) (hq : Node q c) (hv : Node v c) :
    inputCheck q c = inputCheck v c := by
  rw [(inputCheck_exact q c).mpr hq, (inputCheck_exact v c).mpr hv]

theorem argument_comparison_context (q v c d : Nat)
    (hcq : Node q c) (hdq : Node q d) (hcv : Node v c) (hdv : Node v d) :
    Normalization.lessRawCode q (argumentCode c) (argumentCode d) =
      Normalization.lessRawCode v (argumentCode c) (argumentCode d) :=
  OmegaPowers.BaseChange.lessRawCode_context q v _ _
    ((Comparison.acceptedCode_exact q _).mp (node_argument q c hcq)).1
    ((Comparison.acceptedCode_exact q _).mp (node_argument q d hdq)).1
    ((Comparison.acceptedCode_exact v _).mp (node_argument v c hcv)).1
    ((Comparison.acceptedCode_exact v _).mp (node_argument v d hdv)).1

theorem choose_context (q v c : Nat) (tail : Option Nat)
    (hcq : Node q c) (hcv : Node v c)
    (htq : ∀ d, tail = some d → Node q d) (htv : ∀ d, tail = some d → Node v d) :
    choose q c tail = choose v c tail := by
  cases tail with
  | none => rfl
  | some d =>
    simp only [choose, argument_comparison_context q v d c (htq d rfl) hcq (htv d rfl) hcv]

theorem best_context (q v : Nat) (xs : List Nat)
    (hq : ∀ c ∈ xs, Node q c) (hv : ∀ c ∈ xs, Node v c) : best q xs = best v xs := by
  revert hq hv
  induction xs with
  | nil => intro hq hv; rfl
  | cons c xs ih =>
    intro hq hv
    have htq := fun d hd => hq d (List.mem_cons_of_mem c hd)
    have htv := fun d hd => hv d (List.mem_cons_of_mem c hd)
    have he := ih htq htv
    change choose q c (best q xs) = choose v c (best v xs)
    rw [he]
    apply choose_context q v c _ (hq c List.mem_cons_self) (hv c List.mem_cons_self)
    · intro d hd
      have hmem := best_mem v xs d hd
      exact htq d hmem
    · intro d hd
      exact htv d (best_mem v xs d hd)

theorem live_context (q v current : Nat) (xs : List Nat)
    (hcq : Node q current) (hcv : Node v current)
    (hq : ∀ c ∈ xs, Node q c) (hv : ∀ c ∈ xs, Node v c) :
    live q current xs = live v current xs := by
  revert hq hv
  induction xs with
  | nil => intro hq hv; rfl
  | cons c xs ih =>
    intro hq hv
    have he := OmegaPowers.BaseChange.lessRawCode_context q v current c
      (node_checked q current hcq) (node_checked q c (hq c List.mem_cons_self))
      (node_checked v current hcv) (node_checked v c (hv c List.mem_cons_self))
    have ht := ih (fun d hd => hq d (List.mem_cons_of_mem c hd))
      (fun d hd => hv d (List.mem_cons_of_mem c hd))
    simp only [live, he, ht]

theorem walk_context (fuel q v current : Nat) (xs : List Nat)
    (hcq : Node q current) (hcv : Node v current)
    (hq : ∀ c ∈ xs, Node q c) (hv : ∀ c ∈ xs, Node v c) :
    walk fuel q current xs = walk fuel v current xs := by
  induction fuel generalizing current xs with
  | zero => rfl
  | succ fuel ih =>
    have he := best_context q v xs hq hv
    rw [walk_succ, walk_succ, he]
    cases hb : best v xs with
    | none => rfl
    | some c =>
      have hcm := best_mem v xs c hb
      have hncq := hq c hcm
      have hncv := hv c hcm
      have hl := live_context q v c xs hncq hncv hq hv
      rw [hl]
      exact congrArg (List.cons current) (ih c (live v c xs) hncq hncv
        (fun d hd => hq d ((live_mem v c xs d).mp hd).1)
        (fun d hd => hv d ((live_mem v c xs d).mp hd).1))

/-- Genuine original Node admission at both sources licenses every hidden
support comparison, not just the endpoints of the final path. -/
theorem nativePath_context (q v c : Nat) (hcq : Node q c) (hcv : Node v c) :
    nativePath q c = nativePath v c := by
  have hbq := baseRaw_node q (node_baseCheck q c hcq)
  have hbv : Node v (baseRaw q) := by
    simpa only [baseRaw] using baseRaw_node v (node_baseCheck v c hcv)
  have hq := fun d hd => support_node q c d hcq hd
  have hv := fun d hd => support_node v c d hcv hd
  have hl := live_context q v (baseRaw q) (support c) hbq hbv hq hv
  unfold nativePath
  change walk (support c).length q (baseRaw q) (live q (baseRaw q) (support c)) =
    walk (support c).length v (baseRaw q) (live v (baseRaw q) (support c))
  rw [hl]
  exact walk_context _ q v _ _ hbq hbv
    (fun d hd => hq d ((live_mem v _ _ d).mp hd).1)
    (fun d hd => hv d ((live_mem v _ _ d).mp hd).1)

/-- The original chosen Par bound derives the actual transported Node and
literal complete ordinary path without an admission or path oracle. -/
theorem nativePath_change (q v c : Nat) (hc : Node q c) (hv : baseCheck v = true)
    (hp : BaseTransformation.ParBounded q v (rawTree c)) :
    Node v c ∧ nativePath q c = nativePath v c :=
  ⟨node_change q v c hc hv hp, nativePath_context q v c hc (node_change q v c hc hv hp)⟩

end Alexander313.Wilken.RelativeTerm.Hereditary.NativeContext.SourceLocalization.BaseChange
