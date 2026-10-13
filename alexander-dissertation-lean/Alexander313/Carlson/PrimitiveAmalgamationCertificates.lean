import Alexander313.Carlson.AmalgamationCertificates
import Alexander313.Carlson.PrimitiveRationalIso
import Alexander313.Carlson.PrimitiveRationalExactness

/-!
# Machine certification of the original amalgamation verifier

For each finite input dimension, the existing family/product/list codecs
support one total primitive-recursive verifier on all raw candidate codes.
Its finite checks discharge all original amalgamation obligations.
-/

namespace Alexander313.Carlson.PrimitiveAmalgamationCertificates

open Finite AmalgamationCertificate PrimitiveRationalPresentation

abbrev Input (n : ℕ) := (Fin n → RationalPresentation) × AmalgamationCertificate n

variable {n : ℕ} {σ : Type*} [Primcodable σ]

private theorem forall_fin {p : Fin n → σ → Prop} (hp : PrimrecRel p) :
    PrimrecPred (fun s => ∀ i, p i s) :=
  ((PrimitiveFiniteOperations.forall_mem hp).comp
    (Primrec.const (Finset.univ : Finset (Fin n))) Primrec.id).of_eq (fun _ => by simp)

theorem source_primrec : Primrec₂ (fun (i : Fin n) (s : Input n) => s.1 i) :=
  Primrec.fin_app.comp (Primrec.fst.comp Primrec.snd) Primrec.fst

theorem target_primrec : Primrec₂ (fun (_ : Fin n) (s : Input n) => s.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

theorem table_primrec : Primrec₂ (fun (i : Fin n) (s : Input n) => s.2.2.1 i) :=
  Primrec.fin_app.comp (Primrec.fst.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.snd))) Primrec.fst

theorem exactCode_primrec : Primrec₂ (fun (i : Fin n) (s : Input n) => s.2.2.2 i) :=
  Primrec.fin_app.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.snd))) Primrec.fst

theorem imageCarrier_primrec :
    Primrec₂ (fun (i : Fin n) (s : Input n) => (s.1 i).U.image (s.2.maps i)) :=
  (PrimitiveFiniteOperations.finset_image PrimitiveRationalMaps.eval_primrec).comp
    table_primrec (carrier_primrec.comp source_primrec)

theorem image_primrec : Primrec₂ (fun (i : Fin n) (s : Input n) => s.2.image s.1 i) :=
  PrimitiveRationalExactness.restrict_primrec.comp target_primrec imageCarrier_primrec

theorem checkEmbeddings_primrec : Primrec (fun s : Input n => s.2.checkEmbeddings s.1) := by
  have hi : PrimrecRel (fun (i : Fin n) (s : Input n) =>
      PrimitiveRationalIso.IsoData (s.1 i) (s.2.image s.1 i) (s.2.2.1 i)) :=
    PrimitiveRationalIso.isoData_primrec source_primrec image_primrec table_primrec
  refine (forall_fin hi).decide.of_eq ?_
  intro s
  rw [Bool.eq_iff_iff, decide_eq_true_eq, checkEmbeddings_eq_true]
  exact forall_congr' (fun _ => PrimitiveRationalIso.isoData_iff _ _ _)

/-- Compute the union by a finite fold; its result is the original `biUnion`. -/
theorem union_primrec : Primrec (fun s : Input n =>
    Finset.univ.biUnion (fun i => (s.1 i).U.image (s.2.maps i))) := by
  have hlist : Primrec (fun s : Input n => List.ofFn (fun i => (s.1 i).U.image (s.2.maps i))) :=
    Primrec.list_ofFn (fun i => imageCarrier_primrec.comp (Primrec.const i) Primrec.id)
  have hfold : Primrec (fun s : Input n =>
      (List.ofFn (fun i => (s.1 i).U.image (s.2.maps i))).foldr (· ∪ ·) ∅) :=
    Primrec.list_foldr hlist (Primrec.const ∅)
      (PrimitiveFiniteOperations.finset_union.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  refine hfold.of_eq ?_
  intro s
  have hm : ∀ (L : List (Finset ℚ)) x, x ∈ L.foldr (· ∪ ·) ∅ ↔ ∃ U ∈ L, x ∈ U := by
    intro L x
    induction L with
    | nil => simp
    | cons U L ih =>
      simp only [List.foldr_cons, Finset.mem_union, ih, List.mem_cons]
      aesop
  ext x
  simp only [hm, Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_ofFn]
  aesop

theorem check_primrec : Primrec (fun s : Input n => s.2.check s.1) := by
  have hQ : Primrec (fun s : Input n => s.2.1) := Primrec.fst.comp Primrec.snd
  have hx : PrimrecRel (fun (i : Fin n) (s : Input n) =>
      RationalPresentation.checkExact (s.2.image s.1 i) s.2.1 (s.2.2.2 i) = true) :=
    Primrec.eq.comp
      (PrimitiveRationalExactness.checkExact_primrec.comp
        (((show Primrec (fun s : Fin n × Input n => s.2.2.image s.2.1 s.1) from image_primrec).pair
          (show Primrec (fun s : Fin n × Input n => s.2.2.1) from target_primrec)).pair
          (show Primrec (fun s : Fin n × Input n => s.2.2.2.2 s.1) from exactCode_primrec)))
      (Primrec.const true)
  have hu : PrimrecPred (fun s : Input n =>
      s.2.1.U = Finset.univ.biUnion (fun i => (s.1 i).U.image (s.2.maps i))) :=
    Primrec.eq.comp (carrier_primrec.comp hQ) union_primrec
  exact Primrec.and.comp
    (Primrec.and.comp
      (Primrec.and.comp (PrimitiveRationalExactness.checkPattern_primrec.comp hQ)
        checkEmbeddings_primrec) hu.decide) (forall_fin hx).decide

theorem checkCode_primrec : Primrec₂ (fun (P : Fin n → RationalPresentation) code =>
    checkCode P code) := by
  have hstep : Primrec₂ (fun (s : (Fin n → RationalPresentation) × ℕ)
      (c : AmalgamationCertificate n) => c.check s.1) :=
    check_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  refine (Primrec.option_getD.comp
    (Primrec.option_map (Primrec.decode.comp Primrec.snd) hstep)
    (Primrec.const false)).of_eq ?_
  intro s
  unfold checkCode
  cases hd : Encodable.decode (α := AmalgamationCertificate n) s.2 <;> simp [hd]

/-- The existing vector-based encoding of a fixed-size input family,
pinned to the same codec used by the primitive-recursive certification. -/
def familyCode (P : Fin n → RationalPresentation) : ℕ :=
  @Encodable.encode (Fin n → RationalPresentation) Primcodable.finArrow.toEncodable P

@[simp] theorem familyCode_eq (P : Fin n → RationalPresentation) :
    familyCode P = Encodable.encode (List.ofFn P) := by
  change Encodable.encode (List.Vector.ofFn P).toList = Encodable.encode (List.ofFn P)
  rw [List.Vector.toList_ofFn]

theorem checkCode_program (n : ℕ) : ∃ machine : Nat.Partrec.Code,
    ∀ (P : Fin n → RationalPresentation) code,
      machine.eval (Nat.pair (familyCode P) code) =
        Part.some (Encodable.encode (checkCode P code)) := by
  obtain ⟨machine, hm⟩ := exists_code (checkCode_primrec (n := n))
  exact ⟨machine, fun P code => hm (P, code)⟩

end Alexander313.Carlson.PrimitiveAmalgamationCertificates
