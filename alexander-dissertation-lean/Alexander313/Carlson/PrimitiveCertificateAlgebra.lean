import Alexander313.Carlson.PrimitiveGenerationCodec
import Alexander313.Carlson.PrimitiveMinimalityChecks
import Alexander313.Carlson.PrimitiveContinuousEmbeddingChecks

/-!
# Uniform endpoint and checking algebra for finite certificates

The summary stores original encoded endpoints and the existing Boolean check.
These operations also compute endpoints for semantically invalid certificates.
The recursive interpreter validates the original grammar separately.
-/

namespace Alexander313.Carlson.PrimitiveCertificateAlgebra

set_option maxHeartbeats 1200000

open Encodable Finite PrimitivePatternCode PrimitiveFiniteChecks
open PrimitiveReflectionConstructors

abbrev Summary := ℕ × ℕ × Bool

def carrier (n code : ℕ) : Finset ℕ :=
  ((decodeData n code).map Prod.fst).getD ∅

variable {σ : Type*} [Primcodable σ]

theorem carrier_primrec {n code : σ → ℕ} (hn : Primrec n) (hc : Primrec code) :
    Primrec (fun s => carrier (n s) (code s)) :=
  Primrec.option_getD.comp
    ((Primrec.option_map₁ Primrec.fst).comp (decodeData_primrec.comp hn hc))
    (Primrec.const ∅)

@[simp] theorem carrier_encode {n : ℕ} (P : PatternCode n) :
    carrier n (encode P) = carrierView P.U := by
  simp [carrier, decodeData_encode, dataView]

theorem carrier_eq_iff {n : ℕ} (S T : Finset (Fin n)) :
    carrierView S = carrierView T ↔ S = T := by
  constructor
  · intro h
    apply Finset.Subset.antisymm
    · exact (carrierView_subset_iff S T).mp (h.le)
    · exact (carrierView_subset_iff T S).mp (h.symm.le)
  · exact congrArg carrierView

def arithmetic (n p q : ℕ) : Summary :=
  (p, q, PrimitivePatternChecks.checkPattern n p && checkSub n p q &&
    decide (carrier n q = carrier n p))

def downward (n p k a b x s f : ℕ) : Summary :=
  (p, (constructDownward (decide (k = 6)) n p a b s f).getD 0,
    PrimitiveReflectionChecks.checkDownward (decide (k = 6)) n p a b x s f)

def upward (n : ℕ) (d : Summary) (a b s f : ℕ) : Summary :=
  (d.1, (constructUpward n d.1 d.2.1 a b s f).getD 0,
    d.2.2 && PrimitiveReflectionChecks.checkUpward n d.1 d.2.1 a b s f)

def restriction (n : ℕ) (c : Summary) (q a : ℕ) : Summary :=
  (c.1, q, c.2.2 && (checkSub n q c.2.1 &&
    PrimitiveContinuityChecks.checkExtensionAt n c.1 q a))

def lifting (n : ℕ) (d : Summary) (q qplus h f : ℕ) : Summary :=
  (q, qplus, d.2.2 &&
    (PrimitiveContinuousEmbeddingChecks.checkEmbedding n n d.1 q h &&
      PrimitiveLiftingChecks.checkLifting n n d.1 d.2.1 q qplus h f &&
      PrimitiveMinimalityChecks.checkMinimal n n d.1 d.2.1 q qplus h))

def refl (n p : ℕ) : Summary := (p, p, PrimitivePatternChecks.checkPattern n p)

def tail (c d : Summary) : Summary :=
  (c.1, d.2.1, c.2.2 && d.2.2 && decide (c.2.1 = d.1))

theorem arithmetic_primrec {n p q : σ → ℕ}
    (hn : Primrec n) (hp : Primrec p) (hq : Primrec q) :
    Primrec (fun s => arithmetic (n s) (p s) (q s)) := by
  exact hp.pair (hq.pair (Primrec.and.comp
    (Primrec.and.comp (PrimitivePatternChecks.checkPattern_primrec.comp hn hp)
      (checkSub_primrec.comp (hn.pair (hp.pair hq))))
    (Primrec.eq.comp (carrier_primrec hn hq) (carrier_primrec hn hp)).decide))

theorem downward_primrec {n p k a b x s f : σ → ℕ}
    (hn : Primrec n) (hp : Primrec p) (hk : Primrec k) (ha : Primrec a)
    (hb : Primrec b) (hx : Primrec x) (hs : Primrec s) (hf : Primrec f) :
    Primrec (fun t => downward (n t) (p t) (k t) (a t) (b t) (x t) (s t) (f t)) := by
  have hlevel := (Primrec.eq.comp hk (Primrec.const 6)).decide
  have hi := hn.pair (hp.pair (ha.pair (hb.pair (hx.pair (hs.pair hf)))))
  have hcheck : Primrec (fun t =>
      PrimitiveReflectionChecks.checkDownward (decide (k t = 6))
        (n t) (p t) (a t) (b t) (x t) (s t) (f t)) :=
    (Primrec.ite (Primrec.eq.comp hk (Primrec.const 6))
      ((PrimitiveReflectionChecks.checkDownward_primrec true).comp hi)
      ((PrimitiveReflectionChecks.checkDownward_primrec false).comp hi)).of_eq fun t => by
        by_cases h : k t = 6 <;> simp [h]
  exact hp.pair ((Primrec.option_getD.comp
    (constructDownward_comp hlevel hn hp ha hb hs hf) (Primrec.const 0)).pair
    hcheck)

theorem upward_primrec {n a b s f : σ → ℕ} {d : σ → Summary}
    (hn : Primrec n) (hd : Primrec d) (ha : Primrec a)
    (hb : Primrec b) (hs : Primrec s) (hf : Primrec f) :
    Primrec (fun t => upward (n t) (d t) (a t) (b t) (s t) (f t)) := by
  have hp := Primrec.fst.comp hd
  have hq := Primrec.fst.comp (Primrec.snd.comp hd)
  exact hp.pair ((Primrec.option_getD.comp
    (constructUpward_comp hn hp hq ha hb hs hf) (Primrec.const 0)).pair
    (Primrec.and.comp (Primrec.snd.comp (Primrec.snd.comp hd))
      (PrimitiveReflectionChecks.checkUpward_primrec.comp
        (hn.pair (hp.pair (hq.pair (ha.pair (hb.pair (hs.pair hf)))))))))

theorem restriction_primrec {n q a : σ → ℕ} {c : σ → Summary}
    (hn : Primrec n) (hc : Primrec c) (hq : Primrec q) (ha : Primrec a) :
    Primrec (fun s => restriction (n s) (c s) (q s) (a s)) := by
  have hp := Primrec.fst.comp hc
  have ht := Primrec.fst.comp (Primrec.snd.comp hc)
  exact hp.pair (hq.pair (Primrec.and.comp (Primrec.snd.comp (Primrec.snd.comp hc))
    (Primrec.and.comp (checkSub_primrec.comp (hn.pair (hq.pair ht)))
      (PrimitiveContinuityChecks.checkExtensionAt_primrec.comp
        (hn.pair (hp.pair (hq.pair ha)))))))

theorem lifting_primrec {n q qplus h f : σ → ℕ} {d : σ → Summary}
    (hn : Primrec n) (hd : Primrec d) (hq : Primrec q) (hqplus : Primrec qplus)
    (hh : Primrec h) (hf : Primrec f) :
    Primrec (fun s => lifting (n s) (d s) (q s) (qplus s) (h s) (f s)) := by
  have hp := Primrec.fst.comp hd
  have ht := Primrec.fst.comp (Primrec.snd.comp hd)
  exact hq.pair (hqplus.pair (Primrec.and.comp (Primrec.snd.comp (Primrec.snd.comp hd))
    (Primrec.and.comp (Primrec.and.comp
      (PrimitiveContinuousEmbeddingChecks.checkEmbedding_primrec.comp
        (hn.pair (hn.pair (hp.pair (hq.pair hh)))))
      (PrimitiveLiftingChecks.checkLifting_primrec hn hn hp ht hq hqplus hh hf))
      (PrimitiveMinimalityChecks.checkMinimal_primrec hn hn hp ht hq hqplus hh))))

theorem refl_primrec {n p : σ → ℕ} (hn : Primrec n) (hp : Primrec p) :
    Primrec (fun s => refl (n s) (p s)) :=
  hp.pair (hp.pair (PrimitivePatternChecks.checkPattern_primrec.comp hn hp))

theorem tail_primrec {c d : σ → Summary} (hc : Primrec c) (hd : Primrec d) :
    Primrec (fun s => tail (c s) (d s)) :=
  (Primrec.fst.comp hc).pair ((Primrec.fst.comp (Primrec.snd.comp hd)).pair
    (Primrec.and.comp (Primrec.and.comp (Primrec.snd.comp (Primrec.snd.comp hc))
      (Primrec.snd.comp (Primrec.snd.comp hd)))
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp hc))
        (Primrec.fst.comp hd)).decide))

end Alexander313.Carlson.PrimitiveCertificateAlgebra
