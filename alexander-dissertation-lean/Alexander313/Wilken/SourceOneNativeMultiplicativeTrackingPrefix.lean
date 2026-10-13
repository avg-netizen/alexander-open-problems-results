import Alexander313.Wilken.SourceOneNativeTrackingRaw
import Alexander313.Wilken.SourceHighPartComparison

/-!
# Genuine original source-one proper localization prefix callers

The original check-zero localization has strictly descending divided heads
after its initial base. Each selected entry with a later selected entry has
a positive divided head, hence a HIGH original argument and the actual
source-one mu caller. Its RAW epsilon prefix guard follows from its genuine
original admission and epsilon value. No Native base-one parser or supplied
HIGH, epsilon, mu or localization level is used. Uncompiled candidates.
-/

namespace Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.Prefix

open ThetaCourse
open Hereditary.FinePredecessor (stripLast stripLast_primrec)

theorem node_high_of_level_pos (c : Nat) (hc : Localization.Node 0 c)
    (hl : 0 < SourceHighPartComparison.localizationLevel 0 c) : rootCheck c = true := by
  obtain ⟨a, rfl, ha, hn⟩ := hc
  have hca : check 0 a = true := by
    simpa only [Localization.argumentCode_theta, checkCode_code] using
      (Localization.node_argument 0 (.theta 0 a : RelativeTerm Nat).code
        ⟨a, rfl, ha, hn⟩).1
  have hhigh : 1 < a.outerSort := by
    apply lt_of_not_ge
    intro hlo
    have hsmall := (denote_lt_iff_outerSort_le 0 a hca 1 (by omega)).mpr hlo
    have hz : SourceHighPartComparison.localizationLevel 0
        (.theta 0 a : RelativeTerm Nat).code = 0 := by
      simp only [SourceHighPartComparison.localizationLevel, Localization.argumentValue,
        Localization.argumentCode_theta, interpretation_code, SourceHighPartComparison.highPart,
        Ordinal.div_eq_zero_of_lt hsmall, mul_zero]
    rw [hz] at hl
    exact lt_irrefl _ hl
  exact (rootCheck_exact _).mpr ⟨a, rfl, ha, hn, hhigh⟩

theorem sourcePath_proper_tail_high {source : List Nat} {previous : Nat} {tail : List Nat}
    (hp : Localization.SourcePath 0 source (previous :: tail)) (c : Nat)
    (hc : c ∈ stripLast tail) : rootCheck c = true := by
  have hne : tail ≠ [] := by
    intro he
    subst tail
    exact List.not_mem_nil hc
  obtain ⟨d, he, _⟩ := Hereditary.FinePredecessor.stripLast_split tail hne
  have hs := SourceHighPartComparison.sourcePath_levels_descending hp
  rw [he, List.map_append, List.map_cons, List.map_nil] at hs
  have hlt : SourceHighPartComparison.localizationLevel 0 d <
      SourceHighPartComparison.localizationLevel 0 c :=
    (List.pairwise_append.mp hs).2.2 _ (List.mem_map.mpr ⟨c, hc, rfl⟩) _ List.mem_cons_self
  exact node_high_of_level_pos c
    (hp.nodes c (List.mem_cons_of_mem _ (Hereditary.FinePredecessor.stripLast_mem tail c hc)))
    ((show (0 : Ordinal.{0}) ≤ SourceHighPartComparison.localizationLevel 0 d from bot_le).trans_lt hlt)

def properPrefix (root : Nat) : List Nat := stripLast (Localization.nativePath 0 root).tail

theorem properPrefix_primrec : Primrec properPrefix :=
  stripLast_primrec.comp (Primrec.list_tail.comp
    (Localization.nativePath_primrec.comp (Primrec.const 0) Primrec.id))

theorem properPrefix_high (root : Nat) (hi : Localization.inputCheck 0 root = true) :
    ∀ c ∈ properPrefix root, Mu.inputCheck c = true := by
  intro c hc
  obtain ⟨tail, he⟩ := Localization.nativePath_head 0 root
  have hp := Localization.nativePath_source 0 root hi
  rw [he] at hp
  have hm : c ∈ stripLast tail := by simpa only [properPrefix, he, List.tail_cons] using hc
  exact sourcePath_proper_tail_high hp c hm

theorem properPrefix_raw (root : Nat) (hi : Localization.inputCheck 0 root = true) :
    ∀ c ∈ properPrefix root, SourceTrackingRaw.Support.inputCheck c = true := by
  intro c hc
  have hr := properPrefix_high root hi c hc
  exact (SourceTrackingRaw.Support.inputCheck_exact c).mpr
    ⟨root_low c hr, EpsilonOffsets.epsilon_one_lt (root_epsilon c hr), root_epsilon c hr⟩

theorem properPrefix_strict (root : Nat) (hi : Localization.inputCheck 0 root = true) :
    ((properPrefix root).map (interpretation 0)).Pairwise (· < ·) := by
  obtain ⟨tail, he⟩ := Localization.nativePath_head 0 root
  have hp := Localization.nativePath_strict 0 root hi
  rw [he, List.map_cons] at hp
  have ht := (List.pairwise_cons.mp hp).2
  by_cases hn : tail = []
  · simp only [properPrefix, he, List.tail_cons, hn, stripLast, List.reverse_nil,
      List.tail_nil, List.map_nil, List.pairwise_nil]
  · obtain ⟨a, ha, _⟩ := Hereditary.FinePredecessor.stripLast_split tail hn
    rw [ha, List.map_append] at ht
    simpa only [properPrefix, he, List.tail_cons] using (List.pairwise_append.mp ht).1

theorem properPrefix_reverse_strict (root : Nat) (hi : Localization.inputCheck 0 root = true) :
    ((properPrefix root).reverse.map (interpretation 0)).Pairwise (fun a b => b < a) := by
  rw [List.map_reverse]
  exact List.pairwise_reverse.mpr (properPrefix_strict root hi)

theorem properPrefix_le_root (root : Nat) (hi : Localization.inputCheck 0 root = true) :
    ∀ c ∈ properPrefix root, interpretation 0 c ≤ interpretation 0 root := by
  intro c hc
  have hn := (Localization.inputCheck_exact 0 root).mp hi
  obtain ⟨tail, he⟩ := Localization.nativePath_head 0 root
  have hp := Localization.nativePath_source 0 root hi
  rw [he] at hp
  have hm : c ∈ tail := by
    apply Hereditary.FinePredecessor.stripLast_mem tail
    simpa only [properPrefix, he, List.tail_cons] using hc
  exact hp.bounded _ (Localization.baseRaw_le 0 root hn)
    (fun d hd => Localization.support_bound 0 root d hn hd) c (List.mem_cons_of_mem _ hm)

theorem properPrefix_nonempty_root_large (root : Nat) (hi : Localization.inputCheck 0 root = true)
    (hne : properPrefix root ≠ []) : 1 < interpretation 0 root := by
  cases he : properPrefix root with
  | nil => exact False.elim (hne he)
  | cons c cs =>
    have hc : c ∈ properPrefix root := by rw [he]; exact List.mem_cons_self
    have hr := properPrefix_high root hi c hc
    exact (EpsilonOffsets.epsilon_one_lt (root_epsilon c hr)).trans_le
      (properPrefix_le_root root hi c hc)

end Alexander313.Wilken.RelativeTerm.Hereditary.SourceOneIota.SourceMultiplicativeTracking.Prefix
