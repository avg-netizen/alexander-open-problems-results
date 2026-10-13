import Alexander313.RecordedGuards

/-!
# Fresh arithmetic tags and literal holder-local marker padding

Tags have different arithmetic shapes, selected above a finite forbidden
shape pool. Their indices are freely chosen bookkeeping for those shapes,
not codes of ordinal points. Label reflection retains the exact tags and
their order. Every marker label occurs in the padded formula's support.
-/

namespace Alexander313
namespace Shape

def subshapes {Owner : Type} [DecidableEq Owner] : Shape Owner → Finset (Shape Owner)
  | sh@(.falsum) => {sh}
  | sh@(.equal) => {sh}
  | sh@(.imp φ ψ) => insert sh (φ.subshapes ∪ ψ.subshapes)
  | sh@(.conj φ ψ) => insert sh (φ.subshapes ∪ ψ.subshapes)
  | sh@(.disj φ ψ) => insert sh (φ.subshapes ∪ ψ.subshapes)
  | sh@(.neg φ) => insert sh φ.subshapes
  | sh@(.all φ) => insert sh φ.subshapes
  | sh@(.ex φ) => insert sh φ.subshapes
  | sh@(.know _ φ) => insert sh φ.subshapes

end Shape

def markerTag (Owner : Type) : Nat → Formula Owner
  | 0 => .imp .falsum .falsum
  | n + 1 => .imp .falsum (markerTag Owner n)

theorem markerTag_valid (Owner : Type) (n : Nat) : Valid (markerTag Owner n) := by
  cases n <;> intro D hD M s h <;> exact False.elim h

theorem markerTag_closed (Owner : Type) (n : Nat) : (markerTag Owner n).Closed := by
  induction n <;> simp_all [markerTag, Formula.Closed, Formula.freeVars]

theorem markerTag_arithmetic (Owner : Type) (n : Nat) : (markerTag Owner n).Arithmetic := by
  induction n <;> simp_all [markerTag, Formula.Arithmetic]

@[simp] theorem markerTag_rank (Owner : Type) (n : Nat) :
    (markerTag Owner n).shape.rank = 2 * n + 3 := by
  induction n <;> simp_all [markerTag, Formula.shape, Shape.rank] <;> omega

theorem markerTag_shape_injective (Owner : Type) :
    Function.Injective (fun n => (markerTag Owner n).shape) := by
  intro n m h
  have hr := congrArg Shape.rank h
  simp only [markerTag_rank] at hr
  omega

@[simp] theorem markerTag_mapOwner {Owner Other : Type} (f : Owner → Other) (n : Nat) :
    (markerTag Owner n).mapOwner f = markerTag Other n := by
  induction n <;> simp_all [markerTag, Formula.mapOwner]

@[simp] theorem markerTag_support {Owner Label : Type} [DecidableEq Label] (n : Nat) :
    (markerTag (RecordedHead Owner Label) n).labelSupport = ∅ := by
  induction n <;> simp_all [markerTag, Formula.labelSupport]

theorem markerTag_admissible {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (n : Nat) :
    (markerTag (RecordedHead Nat Label) n).RecordedAdmissible A E := by
  induction n <;>
    simp_all [markerTag, Formula.RecordedAdmissible, Formula.HeadsAllowed, Formula.GloballyStratified]

def freshMarkers {Label : Type} (start : Nat) : List Label → List (Label × Nat)
  | [] => []
  | ν :: xs => (ν, start) :: freshMarkers (start + 1) xs

theorem freshMarkers_index_lower {Label : Type} (start : Nat) (xs : List Label)
    {p : Label × Nat} (hp : p ∈ freshMarkers start xs) : start ≤ p.2 := by
  induction xs generalizing start with
  | nil => cases hp
  | cons ν xs ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact le_rfl
    · exact le_trans (Nat.le_succ start) (ih (start + 1) hp)

@[simp] theorem freshMarkers_points {Label : Type} (start : Nat) (xs : List Label) :
    (freshMarkers start xs).map Prod.fst = xs := by
  induction xs generalizing start <;> simp_all [freshMarkers]

theorem freshMarkers_tags_nodup {Label : Type} (start : Nat) (xs : List Label) :
    ((freshMarkers start xs).map Prod.snd).Nodup := by
  induction xs generalizing start with
  | nil => exact List.nodup_nil
  | cons ν xs ih =>
    simp only [freshMarkers, List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (start + 1)⟩
    intro h
    obtain ⟨p, hp, he⟩ := List.mem_map.mp h
    have hl := freshMarkers_index_lower (start + 1) xs hp
    change p.2 = start at he
    omega

theorem freshMarkers_avoid {Label : Type} (F : Finset (Shape Nat)) (xs : List Label)
    {p : Label × Nat} (hp : p ∈ freshMarkers (F.sup Shape.rank + 1) xs) :
    (markerTag Nat p.2).shape ∉ F := by
  intro h
  have hl := freshMarkers_index_lower (F.sup Shape.rank + 1) xs hp
  have hr : (markerTag Nat p.2).shape.rank ≤ F.sup Shape.rank := Finset.le_sup h
  rw [markerTag_rank] at hr
  omega

def markerPoints {Label : Type} [DecidableEq Label] (ms : List (Label × Nat)) : Finset Label :=
  (ms.map Prod.fst).toFinset

/-- Every finite guard-point set has an actual distinct, fresh tag bundle. -/
theorem freshMarkerBundle {Label : Type} [DecidableEq Label]
    (F : Finset (Shape Nat)) (B : Finset Label) :
    ∃ ms : List (Label × Nat), markerPoints ms = B ∧ (ms.map Prod.snd).Nodup ∧
      ∀ p ∈ ms, (markerTag Nat p.2).shape ∉ F := by
  refine ⟨freshMarkers (F.sup Shape.rank + 1) B.toList, ?_,
    freshMarkers_tags_nodup _ _, fun _ hp => freshMarkers_avoid F B.toList hp⟩
  simp [markerPoints]

def markerFormulas {Label : Type} (a : Nat) (ms : List (Label × Nat)) :
    List (Formula (RecordedHead Nat Label)) :=
  ms.map (fun p => .know (.indexed a p.1) (markerTag _ p.2))

def markerPadding {Label : Type} (a : Nat) (ms : List (Label × Nat))
    (φ : Formula (RecordedHead Nat Label)) : Formula (RecordedHead Nat Label) :=
  Formula.chain (markerFormulas a ms) φ

@[simp] theorem markerPadding_support {Label : Type} [DecidableEq Label]
    (a : Nat) (ms : List (Label × Nat)) (φ : Formula (RecordedHead Nat Label)) :
    (markerPadding a ms φ).labelSupport = markerPoints ms ∪ φ.labelSupport := by
  induction ms with
  | nil => simp [markerPadding, markerFormulas, markerPoints, Formula.chain]
  | cons p ms ih =>
    change insert p.1 (markerTag (RecordedHead Nat Label) p.2).labelSupport ∪
      (markerPadding a ms φ).labelSupport = markerPoints (p :: ms) ∪ φ.labelSupport
    rw [markerTag_support, ih]
    simp [markerPoints, Finset.union_assoc, Finset.insert_union]

theorem markerPadding_closed {Label : Type} (a : Nat) (ms : List (Label × Nat))
    (φ : Formula (RecordedHead Nat Label)) (hφ : φ.Closed) :
    (markerPadding a ms φ).Closed := by
  apply Formula.chain_closed _ _ _ hφ
  intro θ hθ
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hθ
  exact markerTag_closed _ p.2

theorem markerPadding_admissible {Label : Type} [DecidableEq Label] [LT Label]
    (A E : Finset Nat) (a : Nat) (ha : a ∈ A) (ms : List (Label × Nat))
    (φ : Formula (RecordedHead Nat Label)) (hφ : φ.RecordedAdmissible A E) :
    (markerPadding a ms φ).RecordedAdmissible A E := by
  apply Formula.recordedAdmissible_chain A E _ φ hφ
  intro θ hθ
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hθ
  apply (Formula.recordedAdmissible_know_indexed A E a p.1 _).mpr
  refine ⟨ha, markerTag_admissible A E p.2, ?_⟩
  intro μ hμ
  rw [markerTag_support] at hμ
  exact False.elim (Finset.notMem_empty μ hμ)

@[simp] theorem markerPadding_relabel {Label : Type} (a : Nat)
    (ms : List (Label × Nat)) (φ : Formula (RecordedHead Nat Label)) (f : Label → Label) :
    (markerPadding a ms φ).relabel f =
      markerPadding a (ms.map (fun p => (f p.1, p.2))) (φ.relabel f) := by
  simp [markerPadding, markerFormulas, Formula.relabel, Formula.mapOwner_chain,
    Formula.mapOwner, RecordedHead.mapLabel, List.map_map, Function.comp_def]

@[simp] theorem markerPoints_relabel {Label : Type} [DecidableEq Label]
    (ms : List (Label × Nat)) (f : Label → Label) :
    markerPoints (ms.map (fun p => (f p.1, p.2))) = (markerPoints ms).image f := by
  ext μ
  constructor
  · intro hμ
    obtain ⟨q, hq, hqμ⟩ := List.mem_map.mp (List.mem_toFinset.mp hμ)
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact Finset.mem_image.mpr ⟨p.1,
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩), hqμ⟩
  · intro hμ
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hμ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hν)
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨(f p.1, p.2), List.mem_map.mpr ⟨p, hp, rfl⟩, rfl⟩)

@[simp] theorem markerPadding_erase {Label : Type} (a : Nat)
    (ms : List (Label × Nat)) (φ : Formula (RecordedHead Nat Label)) :
    (markerPadding a ms φ).erase =
      Formula.chain (ms.map (fun p => .know a (markerTag Nat p.2))) φ.erase := by
  simp [markerPadding, markerFormulas, Formula.erase, Formula.mapOwner_chain,
    Formula.mapOwner, RecordedHead.erase, List.map_map, Function.comp_def]

theorem markerPadding_source_member {R : Nat → Nat → Prop} (C : CommonCorePresentation R)
    {Label : Type} (a : Nat) (ms : List (Label × Nat)) (φ : Formula (RecordedHead Nat Label))
    (hc : φ.Closed) (hφ : C.family.effective.proves a φ.erase) :
    C.family.effective.proves a (markerPadding a ms φ).erase := by
  apply (C.family.theory_closed a _ ((Formula.closed_erase _).mpr
    (markerPadding_closed a ms φ hc))).mp
  rw [markerPadding_erase]
  have hv : Valid (.imp φ.erase
      (Formula.chain (ms.map (fun p => .know a (markerTag Nat p.2))) φ.erase)) := by
    intro D hD M s h
    exact chain_intro M _ φ.erase s (fun _ => h)
  exact (Provable.of_valid hv).modus_ponens (Provable.of_axiom hφ)

end Alexander313
