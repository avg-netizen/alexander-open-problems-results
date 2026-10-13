import Alexander313.Wilken.HereditaryFineLocalizationFirstBranchSupport

/-!
# Actual fine localization lexicographic order

The complete constructed predecessor-gap retention law handles the first
unequal choice across BOTH source branches. Induction on the actual right
FinePath separates roots below, equal to, or above its predecessor. Real
predecessor determinacy handles equality; the derived interval law handles
the mixed open gap. Ordinal trichotomy and genuine List.Lex asymmetry give
the converse. Base singletons and alternate native spellings are retained.

This proves source 2.40 on ordinal VALUE paths of original admitted weak-normal
public theta-zero nodes. It does not assert lex order of native code numbers,
literal support/spelling equality, parameter-support invariance, arbitrary
native-base conversion or the unqualified source 2.37 star clause. The actual
fine search still has no primitive-recursive global length bound. These proof
candidates remain uncompiled and all broad completion obligations remain open.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.FineLocalization.Order

open Localization FinePredecessor FirstBranchSupport

/-- Ordered original roots have genuinely ordered actual fine VALUE paths.
The proof uses the derived first/fallback gap law, not mere Sublist or equal-
root invariance. -/
theorem FinePath.values_lex {r right : Nat} {other : List Nat} (hq : FinePath r right other) :
    ∀ left path, FinePath r left path → value r left < value r right →
      List.Lex (· < ·) (path.map (value r)) (other.map (value r)) := by
  induction hq with
  | base right hr hb =>
    intro left path hp hlr
    have hn := hp.nodes left (by obtain ⟨pre, he⟩ := hp.end; rw [he]; simp)
    have hbase : finiteBase r ≤ value r left := by
      simpa only [baseRaw_value] using baseRaw_le r left hn
    exact False.elim ((hlr.trans_eq hb).not_ge hbase)
  | next right hi other hq ih =>
    intro left path hp hlr
    have hn := hp.nodes left (by obtain ⟨pre, he⟩ := hp.end; rw [he]; simp)
    rcases lt_trichotomy (value r left) (value r (predecessorCode r right)) with h | h | h
    · rw [List.map_append, List.map_cons, List.map_nil]
      exact List.Lex.append_right (· < ·) [value r right] (ih left path hp h)
    · have he := Invariance.FinePath.values_eq hp _ other hq h
      rw [List.map_append, List.map_cons, List.map_nil, he]
      simpa only [List.append_nil] using
        List.Lex.append_left (· < ·) (List.Lex.nil : List.Lex (· < ·) [] [value r right])
          (other.map (value r))
    · exact predecessor_gap_values_lex r right left hi hn h hlr hp (.next right hi other hq)

/-- Literal source 2.40 for every actual original-domain FinePath, including
the base endpoint. Only genuine paths are premises; their original admission
and weak normality are encoded by the constructed recurrence itself. -/
theorem FinePath.values_lex_iff {r left right : Nat} {path other : List Nat}
    (hp : FinePath r left path) (hq : FinePath r right other) :
    List.Lex (· < ·) (path.map (value r)) (other.map (value r)) ↔ value r left < value r right := by
  constructor
  · intro hx
    rcases lt_trichotomy (value r left) (value r right) with h | h | h
    · exact h
    · have he := Invariance.FinePath.values_eq hp right other hq h
      rw [he] at hx
      exact False.elim ((asymm hx) hx)
    · have hy := FinePath.values_lex hp right other hq h
      exact False.elim ((asymm hy) hx)
  · exact FinePath.values_lex hq left path hp

/-- Public spelling invariance was separately proved; here its VALUE paths
also admit the actual strict-order comparison for any two original roots. -/
theorem source_lemma_2_40 (r left right : Nat) (hl : Node r left) (hr : Node r right) :
    ∃ path other, FinePath r left path ∧ FinePath r right other ∧
      (value r left < value r right ↔ List.Lex (· < ·)
        (path.map (value r)) (other.map (value r))) := by
  obtain ⟨path, hp⟩ := finePath_exists r left hl
  obtain ⟨other, hq⟩ := finePath_exists r right hr
  exact ⟨path, other, hp, hq, (FinePath.values_lex_iff hp hq).symm⟩

/-- Denotation of the literal word returned by the already executing search.
Malformed numbers receive an auxiliary empty list outside output contracts. -/
noncomputable def outputValues (r output : Nat) : List Ordinal.{0} :=
  ((Encodable.decode output : Option (List Nat)).getD []).map (value r)

@[simp] theorem outputValues_encode (r : Nat) (path : List Nat) :
    outputValues r (Encodable.encode path) = path.map (value r) := by
  simp only [outputValues, Encodable.encodek, Option.getD_some]

theorem outputValues_source (r root output : Nat) (ho : output ∈ fineLocalization r root) :
    ∃ path, FinePath r root path ∧ outputValues r output = path.map (value r) := by
  obtain ⟨hi, n, hn, he, hp⟩ := fineLocalization_source r root output ho
  exact ⟨FineLocalization.word r root n, hp, by rw [he, outputValues_encode]⟩

/-- The actual returned fine words, not independently supplied paths, have
the literal root-order lex equivalence. -/
theorem outputValues_lex_iff (r left right leftOutput rightOutput : Nat)
    (hl : leftOutput ∈ fineLocalization r left) (hr : rightOutput ∈ fineLocalization r right) :
    List.Lex (· < ·) (outputValues r leftOutput) (outputValues r rightOutput) ↔
      value r left < value r right := by
  obtain ⟨path, hp, he⟩ := outputValues_source r left leftOutput hl
  obtain ⟨other, hq, hf⟩ := outputValues_source r right rightOutput hr
  rw [he, hf]
  exact FinePath.values_lex_iff hp hq

/-- The original raw adapter executes the actual normalized root; both its
original check and exact value preservation are derived from its real domain. -/
theorem rawOutputValues_normalized (r root output : Nat)
    (ho : output ∈ rawFineLocalization r root) :
    output ∈ fineLocalization r (Theta.Normalization.normalizeCode r root) ∧
      value r (Theta.Normalization.normalizeCode r root) = interpretation r root := by
  have hc := (rawFineLocalization_domain r root).mp (Part.dom_iff_mem.mpr ⟨output, ho⟩)
  have hcheck : checkCode r root = true :=
    (Bool.and_eq_true.mp (Bool.and_eq_true.mp hc).1).1
  exact ⟨by simpa only [rawFineLocalization, hc, Bool.cond_true] using ho,
    (Theta.Normalization.normalizeCode_checked r root hcheck).2.2⟩

/-- Actual raw returned words satisfy the same literal VALUE lex equivalence
on the complete original raw proper-theta-zero domain of the existing adapter.
No input Normal, support preservation or native spelling equality is supplied. -/
theorem rawOutputValues_lex_iff (r left right leftOutput rightOutput : Nat)
    (hl : leftOutput ∈ rawFineLocalization r left) (hr : rightOutput ∈ rawFineLocalization r right) :
    List.Lex (· < ·) (outputValues r leftOutput) (outputValues r rightOutput) ↔
      interpretation r left < interpretation r right := by
  have hp := rawOutputValues_normalized r left leftOutput hl
  have hq := rawOutputValues_normalized r right rightOutput hr
  have he := outputValues_lex_iff r _ _ leftOutput rightOutput hp.1 hq.1
  simpa only [hp.2, hq.2] using he

end Alexander313.Wilken.RelativeTerm.Hereditary.FineLocalization.Order
