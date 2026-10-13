import Alexander313.Computability
import Alexander313.Hierarchy
import Alexander313.Specification
import Mathlib.Computability.Primrec.List

/-!
# Positive finite witnesses for whole downward ideals

The frontier and a finite path are literal lists. A certificate checks only
positive edge computations at a finite common cutoff. The search never tests
nonmembership in the hierarchy or its transitive closure. In particular,
well-foundedness and ordinal ranks are not inputs to this compiler.

This is an effective mask prerequisite, not the source-family fixed point or
the whole-ideal genericity theorem. All proof terms await compilation.
-/

namespace Alexander313
namespace PositiveIdeal

def path (R : Nat → Nat → Prop) : List Nat → Nat → Prop
  | [], _ => True
  | v :: vs, j => R v (vs.headD j) ∧ path R vs j

theorem headD_append (xs ys : List Nat) (j : Nat) :
    (xs ++ ys).headD j = xs.headD (ys.headD j) := by
  cases xs <;> rfl

theorem path_append (R : Nat → Nat → Prop) (xs ys : List Nat) (j : Nat) :
    path R (xs ++ ys) j ↔ path R xs (ys.headD j) ∧ path R ys j := by
  induction xs with
  | nil => simp [path]
  | cons v vs ih => simp [path, headD_append, ih, and_assoc]

theorem path_below {R : Nat → Nat → Prop} {xs : List Nat} {j : Nat}
    (h : path R xs j) : xs.headD j = j ∨ StrictBelow R (xs.headD j) j := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons v vs ih =>
    obtain ⟨hv, ht⟩ := h
    rcases ih ht with heq | hb
    · exact Or.inr (.edge (heq ▸ hv))
    · exact Or.inr (.trans (.edge hv) hb)

theorem below_path {R : Nat → Nat → Prop} {i j : Nat}
    (h : StrictBelow R i j) : ∃ xs : List Nat, xs.headD j = i ∧ path R xs j := by
  induction h with
  | @edge i j hij => exact ⟨[i], rfl, hij, trivial⟩
  | @trans i k j _ _ ih₁ ih₂ =>
    obtain ⟨xs, hs, hp⟩ := ih₁
    obtain ⟨ys, ht, hq⟩ := ih₂
    refine ⟨xs ++ ys, ?_, (path_append R xs ys j).mpr ?_⟩
    · rw [headD_append, ht, hs]
    · exact ⟨ht.symm ▸ hp, hq⟩

theorem ideal_iff_path (R : Nat → Nat → Prop) (L : List Nat) (i : Nat) :
    DownIdeal R L.toFinset i ↔
      ∃ j ∈ L, ∃ xs : List Nat, xs.headD j = i ∧ path R xs j := by
  constructor
  · rintro ⟨j, hj, heq | hb⟩
    · exact ⟨j, List.mem_toFinset.mp hj, [], heq.symm, trivial⟩
    · obtain ⟨xs, hs, hp⟩ := below_path hb
      exact ⟨j, List.mem_toFinset.mp hj, xs, hs, hp⟩
  · rintro ⟨j, hj, xs, hs, hp⟩
    refine ⟨j, List.mem_toFinset.mpr hj, ?_⟩
    simpa only [hs] using path_below hp

def edgeTest (c : Program) (k i j : Nat) : Bool :=
  (Nat.Partrec.Code.evaln k c (Nat.pair i j)).isSome

theorem edgeTest_primrec :
    Primrec (fun p : (Program × Nat) × (Nat × Nat) =>
      edgeTest p.1.1 p.1.2 p.2.1 p.2.2) := by
  exact Primrec.option_isSome.comp
    (Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.fst)).pair
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))))

theorem edgeTest_sound {c : Program} {k i j : Nat}
    (h : edgeTest c k i j = true) : c.domain (Nat.pair i j) := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
  exact Part.dom_iff_mem.mpr ⟨y, Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hy)⟩

theorem edgeTest_complete {c : Program} {i j : Nat}
    (h : c.domain (Nat.pair i j)) : ∃ k, edgeTest c k i j = true := by
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp h
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hy
  exact ⟨k, Option.isSome_iff_exists.mpr ⟨y, Option.mem_def.mp hk⟩⟩

theorem edgeTest_mono {c : Program} {k l i j : Nat} (hkl : k ≤ l)
    (h : edgeTest c k i j = true) : edgeTest c l i j = true := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
  exact Option.isSome_iff_exists.mpr ⟨y,
    Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hkl (Option.mem_def.mpr hy))⟩

/-- Backward checking stores the next vertex as well as the accumulated
    Boolean. This makes the path checker a primitive-recursive list fold. -/
def checkedPath (c : Program) (k : Nat) (xs : List Nat) (j : Nat) : Nat × Bool :=
  xs.foldr (fun v state => (v, edgeTest c k v state.1 && state.2)) (j, true)

@[simp] theorem checkedPath_first (c : Program) (k : Nat) (xs : List Nat) (j : Nat) :
    (checkedPath c k xs j).1 = xs.headD j := by
  cases xs <;> rfl

theorem checkedPath_primrec :
    Primrec (fun p : (Program × Nat) × (List Nat × Nat) =>
      checkedPath p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hf : Primrec (fun p : (Program × Nat) × (List Nat × Nat) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hg : Primrec (fun p : (Program × Nat) × (List Nat × Nat) => (p.2.2, true)) :=
    (Primrec.snd.comp Primrec.snd).pair (Primrec.const true)
  have hstep : Primrec₂ (fun (p : (Program × Nat) × (List Nat × Nat))
      (s : Nat × (Nat × Bool)) =>
      (s.1, edgeTest p.1.1 p.1.2 s.1 s.2.1 && s.2.2)) := by
    have hv : Primrec (fun p : ((Program × Nat) × (List Nat × Nat)) ×
        (Nat × (Nat × Bool)) => p.2.1) := Primrec.fst.comp Primrec.snd
    have hn : Primrec (fun p : ((Program × Nat) × (List Nat × Nat)) ×
        (Nat × (Nat × Bool)) => p.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hb : Primrec (fun p : ((Program × Nat) × (List Nat × Nat)) ×
        (Nat × (Nat × Bool)) => p.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have he := edgeTest_primrec.comp
      ((Primrec.fst.comp Primrec.fst).pair (hv.pair hn))
    exact (hv.pair (Primrec.and.comp he hb)).to₂
  exact Primrec.list_foldr hf hg hstep

theorem checkedPath_iff (c : Program) (k : Nat) (xs : List Nat) (j : Nat) :
    (checkedPath c k xs j).2 = true ↔
      path (fun i j => edgeTest c k i j = true) xs j := by
  induction xs with
  | nil => simp [checkedPath, path]
  | cons v vs ih =>
    change (edgeTest c k v (checkedPath c k vs j).1 &&
      (checkedPath c k vs j).2) = true ↔
      edgeTest c k v (vs.headD j) = true ∧
        path (fun i j => edgeTest c k i j = true) vs j
    rw [Bool.and_eq_true, checkedPath_first, ih]

theorem path_mono {R S : Nat → Nat → Prop}
    (hRS : ∀ i j, R i j → S i j) (xs : List Nat) (j : Nat) :
    path R xs j → path S xs j := by
  induction xs with
  | nil => exact fun _ => trivial
  | cons v vs ih => exact fun h => ⟨hRS _ _ h.1, ih h.2⟩

theorem checkedPath_sound (c : Program) (k : Nat) (xs : List Nat) (j : Nat)
    (h : (checkedPath c k xs j).2 = true) :
    path (fun i j => c.domain (Nat.pair i j)) xs j :=
  path_mono (fun _ _ => edgeTest_sound) xs j ((checkedPath_iff c k xs j).mp h)

theorem checkedPath_complete (c : Program) (xs : List Nat) (j : Nat)
    (h : path (fun i j => c.domain (Nat.pair i j)) xs j) :
    ∃ k, (checkedPath c k xs j).2 = true := by
  induction xs with
  | nil => exact ⟨0, rfl⟩
  | cons v vs ih =>
    obtain ⟨k, hk⟩ := edgeTest_complete h.1
    obtain ⟨l, hl⟩ := ih h.2
    refine ⟨max k l, (checkedPath_iff c (max k l) (v :: vs) j).mpr ?_⟩
    refine ⟨edgeTest_mono (Nat.le_max_left k l) hk, ?_⟩
    exact path_mono (fun _ _ => edgeTest_mono (Nat.le_max_right k l)) vs j
      ((checkedPath_iff c l vs j).mp hl)

def listContains (L : List Nat) (n : Nat) : Bool :=
  L.foldr (fun a b => (a == n) || b) false

@[simp] theorem listContains_iff (L : List Nat) (n : Nat) :
    listContains L n = true ↔ n ∈ L := by
  induction L with
  | nil => simp [listContains]
  | cons a L ih =>
    rw [List.mem_cons]
    change ((a == n) || listContains L n) = true ↔ n = a ∨ n ∈ L
    rw [Bool.or_eq_true, beq_iff_eq, ih]
    exact or_congr eq_comm Iff.rfl

theorem listContains_primrec : Primrec₂ listContains := by
  exact (Primrec.list_foldr Primrec.fst (Primrec.const false)
    ((Primrec.or.comp
      (Primrec.beq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd)).to₂)).to₂

def decodePath (n : Nat) : List Nat := (Encodable.decode (α := List Nat) n).getD []

theorem decodePath_primrec : Primrec decodePath :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

@[simp] theorem decodePath_encode (xs : List Nat) :
    decodePath (Encodable.encode xs) = xs := by simp [decodePath]

/-- `w` codes endpoint, path, and time bound, all positive finite data. -/
def certificate (c : Program) (L : List Nat) (i w : Nat) : Bool :=
  let j := w.unpair.1
  let xs := decodePath w.unpair.2.unpair.1
  let k := w.unpair.2.unpair.2
  let result := checkedPath c k xs j
  listContains L j && ((i == result.1) && result.2)

theorem certificate_primrec :
    Primrec (fun p : (Program × List Nat) × (Nat × Nat) =>
      certificate p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : (Program × List Nat) × (Nat × Nat) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hL : Primrec (fun p : (Program × List Nat) × (Nat × Nat) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun p : (Program × List Nat) × (Nat × Nat) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hw : Primrec (fun p : (Program × List Nat) × (Nat × Nat) => p.2.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.snd)
  have hj := Primrec.fst.comp hw
  have hrest := Primrec.unpair.comp (Primrec.snd.comp hw)
  have hxs := decodePath_primrec.comp (Primrec.fst.comp hrest)
  have hk := Primrec.snd.comp hrest
  have hp := checkedPath_primrec.comp ((hc.pair hk).pair (hxs.pair hj))
  exact Primrec.and.comp (listContains_primrec.comp hL hj)
    (Primrec.and.comp (Primrec.beq.comp hi (Primrec.fst.comp hp)) (Primrec.snd.comp hp))

theorem certificate_iff (c : Program) (L : List Nat) (i : Nat) :
    (∃ w, certificate c L i w = true) ↔
      DownIdeal (fun a b => c.domain (Nat.pair a b)) L.toFinset i := by
  rw [ideal_iff_path]
  constructor
  · rintro ⟨w, hw⟩
    have h := hw
    simp only [certificate, Bool.and_eq_true, beq_iff_eq,
      listContains_iff, checkedPath_first] at h
    exact ⟨w.unpair.1, h.1, decodePath w.unpair.2.unpair.1, h.2.1.symm,
      checkedPath_sound c _ _ _ h.2.2⟩
  · rintro ⟨j, hj, xs, hs, hp⟩
    obtain ⟨k, hk⟩ := checkedPath_complete c xs j hp
    refine ⟨Nat.pair j (Nat.pair (Encodable.encode xs) k), ?_⟩
    simp only [certificate, Nat.unpair_pair, decodePath_encode, Bool.and_eq_true,
      listContains_iff, beq_iff_eq]
    exact ⟨hj, ((checkedPath_first c k xs j).trans hs).symm, hk⟩

def evaluation (e i : Nat) : Part Nat :=
  let c := Nat.Partrec.Code.ofNatCode e.unpair.1
  let L := decodePath e.unpair.2
  Nat.rfindOpt (fun w => cond (certificate c L i w) (some 0) none)

theorem evaluation_partrec : Partrec₂ evaluation := by
  have hc : Primrec (fun p : (Nat × Nat) × Nat =>
      Nat.Partrec.Code.ofNatCode p.1.1.unpair.1) := (Primrec.ofNat Program).comp
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)))
  have hL : Primrec (fun p : (Nat × Nat) × Nat => decodePath p.1.1.unpair.2) :=
    decodePath_primrec.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)))
  have hi : Primrec (fun p : (Nat × Nat) × Nat => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have ht := certificate_primrec.comp ((hc.pair hL).pair (hi.pair Primrec.snd))
  exact (Partrec.rfindOpt ((ht.cond (Primrec.const (some 0))
    (Primrec.const none)).to_comp.to₂)).to₂

theorem evaluation_domain (e i : Nat) :
    (evaluation e i).Dom ↔
      DownIdeal (fun a b => Program.domain (Nat.Partrec.Code.ofNatCode e.unpair.1)
        (Nat.pair a b)) (decodePath e.unpair.2).toFinset i := by
  rw [evaluation, Nat.rfindOpt_dom, ← certificate_iff]
  constructor
  · rintro ⟨w, y, hy⟩
    cases h : certificate (Nat.Partrec.Code.ofNatCode e.unpair.1)
      (decodePath e.unpair.2) i w <;> simp [h] at hy
    exact ⟨w, h⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, 0, by simp [hw]⟩

/-- One fixed search kernel and s-m-n give a primitive-recursive compiler
    uniformly in the edge program and the literal finite frontier. -/
theorem compiler_exists :
    ∃ compiler : Program × List Nat → Program, Primrec compiler ∧
      ∀ c L i, (compiler (c, L)).domain i ↔
        DownIdeal (fun a b => c.domain (Nat.pair a b)) L.toFinset i := by
  obtain ⟨kernel, hkernel⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec₂.unpaired'.mpr evaluation_partrec)
  refine ⟨fun p => Nat.Partrec.Code.curry kernel
    (Nat.pair (Encodable.encode p.1) (Encodable.encode p.2)), ?_, ?_⟩
  · exact Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const kernel)
      (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
        (Primrec.encode.comp Primrec.snd))
  · intro c L i
    change ((Nat.Partrec.Code.curry kernel _).eval i).Dom ↔ _
    rw [Nat.Partrec.Code.eval_curry, hkernel]
    have hc : Nat.Partrec.Code.ofNatCode (Encodable.encode c) = c :=
      Denumerable.ofNat_encode c
    simpa [Nat.unpaired, Nat.unpair_pair, hc] using
      evaluation_domain (Nat.pair (Encodable.encode c) (Encodable.encode L)) i

theorem hierarchy_program {R : Nat → Nat → Prop} (hR : HierarchyRE R) :
    ∃ c : Program, ∀ i j, c.domain (Nat.pair i j) ↔ R i j := by
  have hp : Partrec (fun n : Nat =>
      Part.assert (R n.unpair.1 n.unpair.2) (fun _ => Part.some ())) :=
    hR.comp Primrec.unpair.to_comp
  have hm := hp.map ((Computable.const (0 : Nat)).to₂)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hm)
  refine ⟨c, fun i j => ?_⟩
  change (c.eval (Nat.pair i j)).Dom ↔ R i j
  rw [hc]
  simp [Part.map, Part.assert, Part.some, Nat.unpair_pair]

theorem hierarchy_ideal_program {R : Nat → Nat → Prop}
    (hR : HierarchyRE R) (J : Finset Nat) :
    ∃ c : Program, ∀ i, c.domain i ↔ DownIdeal R J i := by
  classical
  obtain ⟨edge, hedge⟩ := hierarchy_program hR
  obtain ⟨compiler, _, hcompiler⟩ := compiler_exists
  have hrel : (fun a b => edge.domain (Nat.pair a b)) = R := by
    funext a b
    exact propext (hedge a b)
  refine ⟨compiler (edge, J.toList), fun i => ?_⟩
  simpa [hrel] using hcompiler edge J.toList i

theorem hierarchy_ideal_re {R : Nat → Nat → Prop}
    (hR : HierarchyRE R) (J : Finset Nat) : REPred (DownIdeal R J) := by
  obtain ⟨c, hc⟩ := hierarchy_ideal_program hR J
  exact (program_domain_re c).of_eq hc

end PositiveIdeal
end Alexander313
