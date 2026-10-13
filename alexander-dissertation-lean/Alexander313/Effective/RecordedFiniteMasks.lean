import Alexander313.RecordedFiniteTables
import Alexander313.Alexander.LiteralCoding
import Alexander313.Effective.RecordedTreeFold
import Alexander313.Effective.RecordedGuardPrograms

/-!
# Actual query-key and hereditary-mask checks

The code fold visits the original source tree. A modal head contributes the
pair of its actual owner and its whole argument's erased shape code. Binary
branches append; negations and quantifiers retain all nested queries. Typed
formula representatives avoid requiring a primitive coding instance for
`Shape Nat`. Invalid raw codes have total values; the mask itself is typed.
-/

noncomputable section

namespace Alexander313.RecordedTable

open RecordedFormula
open RecordedGuardProgram (allCheck allCheck_iff allCheck_primrec)

def maskKeys (M : Mask) : List Nat :=
  M.map (fun p => Nat.pair p.1 p.2.shape.code)

theorem maskKeys_primrec : Primrec maskKeys := by
  have hp : Primrec (fun p : Nat × Formula Nat => Nat.pair p.1 p.2.shape.code) := by
    simpa only [Formula.shapeCode_code] using
      Primrec₂.natPair.comp Primrec.fst
        (Formula.shapeCode_primrec.comp (Formula.code_primrec.comp Primrec.snd))
  exact Primrec.list_map Primrec.id (hp.comp Primrec.snd).to₂

@[simp] theorem mem_maskKeys (M : Mask) (a : Nat) (sh : Shape Nat) :
    Nat.pair a sh.code ∈ maskKeys M ↔ (a, sh) ∈ mask M := by
  rw [mem_mask]
  simp only [maskKeys, List.mem_map]
  constructor
  · rintro ⟨⟨b, φ⟩, hp, he⟩
    have h := Nat.pair_eq_pair.mp he
    have hb : b = a := h.1
    have hs := Shape.code_injective h.2
    subst b
    exact ⟨φ, hp, hs⟩
  · rintro ⟨φ, hp, hs⟩
    exact ⟨(a, φ), hp, by simp only [hs]⟩

def queryKeys (φ : Formula Nat) : List Nat :=
  φ.queryList.map (fun p => queryKey p.1 p.2)

@[simp] theorem mem_queryKeys (φ : Formula Nat) (a : Nat) (sh : Shape Nat) :
    queryKey a sh ∈ queryKeys φ ↔ (a, sh) ∈ φ.queries := by
  simp only [queryKeys, List.mem_map, Formula.mem_queryList]
  constructor
  · rintro ⟨p, hp, he⟩
    have hpq : p = (a, sh) := queryKey_injective he
    simpa only [hpq] using hp
  · intro hp
    exact ⟨(a, sh), hp, rfl⟩

def queryKeysCode (n : Nat) : List Nat :=
  ValueFold.code List.append id []
    (fun (_ : Unit) owner argument tail => Nat.pair owner (Formula.shapeCode argument) :: tail) () n

theorem queryKeysCode_primrec : Primrec queryKeysCode := by
  have hh : Primrec (fun p : Unit × (Nat × (Nat × List Nat)) =>
      Nat.pair p.2.1 (Formula.shapeCode p.2.2.1) :: p.2.2.2) := by
    have ho : Primrec (fun p : Unit × (Nat × (Nat × List Nat)) => p.2.1) :=
      Primrec.fst.comp Primrec.snd
    have ht : Primrec (fun p : Unit × (Nat × (Nat × List Nat)) => p.2.2) :=
      Primrec.snd.comp Primrec.snd
    exact Primrec.list_cons.comp
      (Primrec₂.natPair.comp ho (Formula.shapeCode_primrec.comp (Primrec.fst.comp ht)))
      (Primrec.snd.comp ht)
  exact (ValueFold.code_primrec List.append id [] _ Primrec.list_append Primrec.id hh).comp
    (Primrec.const ()) Primrec.id

@[simp] theorem queryKeysCode_formula (φ : Formula Nat) :
    queryKeysCode (φ.code id) = queryKeys φ := by
  induction φ <;>
    simp_all [queryKeysCode, ValueFold.code, Formula.code, EncodedSyntax.node,
      Nat.unpair_pair, queryKeys, Formula.queryList, queryKey]

theorem queryKeys_primrec : Primrec queryKeys := by
  simpa only [queryKeysCode_formula] using queryKeysCode_primrec.comp Formula.code_primrec

theorem queryKeys_subset_exact (M : Mask) (φ : Formula Nat) :
    (∀ key ∈ queryKeys φ, listMember (maskKeys M) key = true) ↔
      φ.shape.queries ⊆ mask M := by
  rw [Formula.queries_shape]
  constructor
  · intro h q hq
    rcases q with ⟨a, sh⟩
    exact (mem_maskKeys M a sh).mp
      (of_decide_eq_true (h (queryKey a sh) ((mem_queryKeys φ a sh).mpr hq)))
  · intro h key hk
    obtain ⟨⟨a, sh⟩, hq, he⟩ := List.mem_map.mp hk
    subst key
    simp only [listMember, decide_eq_true_eq]
    exact (mem_maskKeys M a sh).mpr (h ((Formula.mem_queryList φ (a, sh)).mp hq))

def hereditaryCheck (M : Mask) : Bool :=
  allCheck (fun p => allCheck (listMember (maskKeys M)) (queryKeysCode (p.2.code id))) M

theorem hereditaryCheck_primrec : Primrec hereditaryCheck := by
  have ht : Primrec₂ (fun (M : Mask) (p : Nat × Formula Nat) =>
      allCheck (listMember (maskKeys M)) (queryKeysCode (p.2.code id))) :=
    ((allCheck_primrec listMember listMember_primrec).comp
      (maskKeys_primrec.comp Primrec.fst)
      (queryKeysCode_primrec.comp
        (Formula.code_primrec.comp (Primrec.snd.comp Primrec.snd)))).to₂
  exact (allCheck_primrec _ ht).comp Primrec.id Primrec.id

theorem hereditaryCheck_exact (M : Mask) :
    hereditaryCheck M = true ↔ HereditaryQueries (mask M) := by
  simp only [hereditaryCheck, allCheck_iff, queryKeysCode_formula, queryKeys_subset_exact]
  constructor
  · intro h a sh hm
    obtain ⟨φ, hφ, hs⟩ := (mem_mask M a sh).mp hm
    simpa only [hs] using h (a, φ) hφ
  · intro h p hp
    exact h p.1 p.2.shape ((mem_mask M p.1 p.2.shape).mpr ⟨p.2, hp, rfl⟩)

end Alexander313.RecordedTable
