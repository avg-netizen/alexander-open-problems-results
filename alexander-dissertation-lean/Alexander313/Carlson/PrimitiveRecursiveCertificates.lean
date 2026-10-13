import Alexander313.Carlson.PrimitiveReflectionConstructors
import Alexander313.Carlson.PrimitiveSExpression
import Alexander313.Carlson.FiniteCertificates
import Batteries.Tactic.OpenPrivate

/-!
# Primitive recursion for the original mutual finite certificate codes

The interpreter retains atom fields, decoded rules, decoded chains and list
spines separately. Recursive fields are trees; scalar fields are atoms whose
contents use the existing component codecs. The distinction is checked even
on malformed inputs. Both certificate kinds are interpreted in one tree fold.
-/

namespace Alexander313.Carlson.PrimitiveRecursiveCertificates

set_option maxHeartbeats 400000

open Encodable Finite PrimitivePatternCode PrimitiveFiniteFunctions

abbrev Entry := Option ℕ × Option ℕ × Option ℕ
abbrev Value := Entry × Option (List Entry)

/-- Encode one atom in the pinned derived tree format. -/
def atomCode (x : ℕ) : ℕ := Nat.pair 0 x

/-- Encode a node whose fields have already been converted to tree codes. -/
def nodeCode (tag : ℕ) (fields : List ℕ) : ℕ :=
  Nat.pair (atomCode tag + 1)
    (fields.foldr (fun h t => Nat.pair (h + 1) t) (atomCode 0))

theorem atomCode_primrec : Primrec atomCode :=
  Primrec₂.natPair.comp (Primrec.const 0) Primrec.id

theorem nodeCode_primrec : Primrec₂ nodeCode := by
  have hstep : Primrec₂ (fun (_ : ℕ × List ℕ) (p : ℕ × ℕ) =>
      Nat.pair (p.1 + 1) p.2) :=
    (Primrec₂.natPair.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  have hfold : Primrec (fun p : ℕ × List ℕ =>
      p.2.foldr (fun h t => Nat.pair (h + 1) t) (atomCode 0)) :=
    Primrec.list_foldr (h := fun (_ : ℕ × List ℕ) (p : ℕ × ℕ) =>
      Nat.pair (p.1 + 1) p.2) Primrec.snd (Primrec.const (atomCode 0)) hstep
  have htag : Primrec (fun p : ℕ × List ℕ => atomCode p.1 + 1) :=
    Primrec.succ.comp (atomCode_primrec.comp Primrec.fst)
  exact (Primrec₂.natPair.comp htag hfold).to₂

/-- Canonical scalar fields: pattern, level, label, carrier, total map.
The last two kinds select a recursively interpreted rule or chain. -/
def field (n kind : ℕ) (e : Entry) : Option ℕ :=
  if kind = 5 then e.2.1 else if kind = 6 then e.2.2 else
    e.1.bind fun c =>
      (if kind = 0 then normalize n c
      else if kind = 1 then if c = 2 ∨ c = 6 then some c else none
      else if kind = 2 then decodeLabel n c
      else if kind = 3 then (decodeCarrier n c).map encode
      else if kind = 4 then normalizeArrowWith (decodeLabel n) n c
      else none).map atomCode

theorem field_primrec : Primrec (fun p : ℕ × ℕ × Entry => field p.1 p.2.1 p.2.2) := by
  unfold field
  refine Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 5))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) ?_
  refine Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 6))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) ?_
  refine Primrec.option_bind (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) ?_
  apply Primrec₂.mk
  refine Primrec.option_map ?_ (atomCode_primrec.comp Primrec.snd).to₂
  have hn : Primrec (fun p : (ℕ × ℕ × Entry) × ℕ => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hk : Primrec (fun p : (ℕ × ℕ × Entry) × ℕ => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  refine Primrec.ite (Primrec.eq.comp hk (Primrec.const 0))
    (normalize_primrec.comp hn Primrec.snd) ?_
  refine Primrec.ite (Primrec.eq.comp hk (Primrec.const 1)) ?_ ?_
  · exact Primrec.ite ((Primrec.eq.comp Primrec.snd (Primrec.const 2)).or
      (Primrec.eq.comp Primrec.snd (Primrec.const 6)))
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  refine Primrec.ite (Primrec.eq.comp hk (Primrec.const 2))
    (decodeLabel_primrec.comp hn Primrec.snd) ?_
  refine Primrec.ite (Primrec.eq.comp hk (Primrec.const 3))
    ((Primrec.option_map₁ Primrec.encode).comp (decodeCarrier_primrec.comp hn Primrec.snd)) ?_
  refine Primrec.ite (Primrec.eq.comp hk (Primrec.const 4)) ?_ (Primrec.const none)
  exact normalizeArrowWith_primrec
    (decodeLabel_primrec.comp (hn.comp Primrec.fst) Primrec.snd).to₂ hn Primrec.snd

/-- Traverse a finite list of optional results without silently discarding
failed fields. -/
def collect (xs : List (Option ℕ)) : Option (List ℕ) :=
  xs.foldr (fun x rest => x.bind fun a => rest.map (a :: ·)) (some [])

theorem collect_primrec : Primrec collect := by
  unfold collect
  refine Primrec.list_foldr
    (h := fun (_ : List (Option ℕ)) (p : Option ℕ × Option (List ℕ)) =>
      p.1.bind fun a => p.2.map (a :: ·))
    Primrec.id (Primrec.const (some [])) ?_
  apply Primrec₂.mk
  refine Primrec.option_bind (Primrec.fst.comp Primrec.snd) ?_
  apply Primrec₂.mk
  exact Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

def fields (n : ℕ) (schema : List ℕ) (args : List Entry) : Option (List ℕ) :=
  if args.length = schema.length then
    collect ((List.range schema.length).map fun i =>
      field n (schema.getD i 7) (args.getD i (none, none, none)))
  else none

theorem fields_primrec :
    Primrec (fun p : ℕ × List ℕ × List Entry => fields p.1 p.2.1 p.2.2) := by
  unfold fields
  have hs : Primrec (fun p : ℕ × List ℕ × List Entry => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : ℕ × List ℕ × List Entry => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  refine Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp ha)
    (Primrec.list_length.comp hs)) ?_ (Primrec.const none)
  refine collect_primrec.comp (Primrec.list_map
    (Primrec.list_range.comp (Primrec.list_length.comp hs)) ?_)
  exact (field_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
    (((Primrec.list_getD 7).comp (hs.comp Primrec.fst) Primrec.snd).pair
      ((Primrec.list_getD (none, none, none)).comp (ha.comp Primrec.fst)
        Primrec.snd)))).to₂

theorem fields_comp_primrec {σ : Type*} [Primcodable σ]
    {n : σ → ℕ} {schema : σ → List ℕ} {args : σ → List Entry}
    (hn : Primrec n) (hs : Primrec schema) (ha : Primrec args) :
    Primrec (fun s => fields (n s) (schema s) (args s)) :=
  fields_primrec.comp (hn.pair (hs.pair ha))


private theorem collect_cons (a : Option ℕ) (l : List (Option ℕ)) :
    collect (a :: l) = a.bind (fun x => (collect l).map (x :: ·)) := rfl

private theorem fields_nil (n : ℕ) (args : List Entry) :
    fields n [] args = if args = [] then some [] else none := by
  cases args <;> simp [fields, collect]

private theorem fields_emptyargs (n k : ℕ) (ks : List ℕ) :
    fields n (k :: ks) [] = none := by simp [fields]

private theorem fields_cons (n k : ℕ) (ks : List ℕ) (e : Entry) (es : List Entry) :
    fields n (k :: ks) (e :: es) =
      (field n k e).bind fun x => (fields n ks es).map (x :: ·) := by
  by_cases h : es.length = ks.length
  · simp only [fields, List.length_cons, h, ↓reduceIte, List.range_succ_eq_map,
      List.map_cons, List.getD_cons_zero, List.map_map, Function.comp_def,
      List.getD_cons_succ]
    rfl
  · simp only [fields, List.length_cons, Nat.add_right_cancel_iff, h, ↓reduceIte,
      Option.map_none]
    cases field n k e <;> rfl

def ruleSchemas : List (List ℕ) :=
  [[0, 0], [0, 1, 2, 2, 3, 3, 4], [5, 2, 2, 3, 4], [6, 0, 2], [5, 0, 0, 4, 4]]

def chainSchemas : List (List ℕ) := [[0], [6, 5]]

def interpret (n : ℕ) (schemas : List (List ℕ))
    (tag : Option ℕ) (args : Option (List Entry)) : Option ℕ :=
  tag.bind fun k => (schemas[k]?).bind fun schema =>
    args.bind fun entries => (fields n schema entries).map (nodeCode k)

theorem interpret_primrec : Primrec
    (fun p : ℕ × List (List ℕ) × Option ℕ × Option (List Entry) =>
      interpret p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := ℕ × List (List ℕ) × Option ℕ × Option (List Entry)
  have hb : Primrec (fun p : ((A × ℕ) × List ℕ) × List Entry =>
      (fields p.1.1.1.1 p.1.2 p.2).map (nodeCode p.1.1.2)) := by
    let B := ((A × ℕ) × List ℕ) × List Entry
    have hn : Primrec (fun p : B => p.1.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hs : Primrec (fun p : B => p.1.2) := Primrec.snd.comp Primrec.fst
    have he : Primrec (fun p : B => p.2) := Primrec.snd
    have hk : Primrec (fun p : B => p.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hf : Primrec (fun p : B => fields p.1.1.1.1 p.1.2 p.2) :=
      fields_comp_primrec hn hs he
    exact Primrec.option_map hf (nodeCode_primrec.comp (hk.comp Primrec.fst) Primrec.snd).to₂
  have he : Primrec (fun p : (A × ℕ) × List ℕ =>
      p.1.1.2.2.2.bind fun entries =>
        (fields p.1.1.1 p.2 entries).map (nodeCode p.1.2)) :=
    Primrec.option_bind
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.fst.comp Primrec.fst)))) hb.to₂
  have hk : Primrec (fun p : A × ℕ =>
      (p.1.2.1[p.2]?).bind fun schema => p.1.2.2.2.bind fun entries =>
        (fields p.1.1 schema entries).map (nodeCode p.2)) :=
    Primrec.option_bind (Primrec.list_getElem?.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd) he.to₂
  exact Primrec.option_bind (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hk.to₂

def atom (_n x : ℕ) : Value :=
  ((some x, none, none), if x = 0 then some [] else none)

def cons (n : ℕ) (h t : Value) : Value :=
  ((none, interpret n ruleSchemas h.1.1 t.2,
    interpret n chainSchemas h.1.1 t.2), t.2.map (h.1 :: ·))

theorem atom_primrec : Primrec₂ atom := by
  unfold atom
  exact (((Primrec.option_some.comp Primrec.snd).pair
    ((Primrec.const none).pair (Primrec.const none))).pair
      (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
        (Primrec.const (some [])) (Primrec.const none))).to₂

theorem cons_primrec : Primrec (fun p : ℕ × Value × Value => cons p.1 p.2.1 p.2.2) := by
  unfold cons
  have hh : Primrec (fun p : ℕ × Value × Value => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have ht : Primrec (fun p : ℕ × Value × Value => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hi (schemas : List (List ℕ)) : Primrec
      (fun p : ℕ × Value × Value => interpret p.1 schemas p.2.1.1.1 p.2.2.2) :=
    interpret_primrec.comp (Primrec.fst.pair ((Primrec.const schemas).pair
      ((Primrec.fst.comp hh).pair ht)))
  exact ((Primrec.const none).pair ((hi ruleSchemas).pair (hi chainSchemas))).pair
    (Primrec.option_map ht (Primrec.list_cons.comp (hh.comp Primrec.fst) Primrec.snd).to₂)

def evaluate (n code : ℕ) : Value := PrimitiveSExpression.fold atom cons n code

theorem evaluate_primrec : Primrec₂ evaluate :=
  PrimitiveSExpression.fold_primrec atom_primrec cons_primrec

def normalizeRule (n code : ℕ) : Option ℕ := (evaluate n code).1.2.1
def normalizeChain (n code : ℕ) : Option ℕ := (evaluate n code).1.2.2

theorem normalizeRule_primrec : Primrec₂ normalizeRule :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp evaluate_primrec))).to₂

theorem normalizeChain_primrec : Primrec₂ normalizeChain :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp evaluate_primrec))).to₂




@[simp] theorem evaluate_atom (n x : ℕ) :
    evaluate n (atomCode x) = atom n x := PrimitiveSExpression.fold_atom atom cons n x

@[simp] theorem evaluate_cons (n h t : ℕ) :
    evaluate n (Nat.pair (h + 1) t) = cons n (evaluate n h) (evaluate n t) :=
  PrimitiveSExpression.fold_cons atom cons n h t

private theorem evaluate_fields (n : ℕ) (xs : List ℕ) :
    (evaluate n (xs.foldr (fun h t => Nat.pair (h + 1) t) (atomCode 0))).2 =
      some (xs.map fun c => (evaluate n c).1) := by
  induction xs with
  | nil => simp [evaluate, atomCode, atom]
  | cons c xs ih =>
      simp only [List.foldr_cons, evaluate, PrimitiveSExpression.fold_cons]
      change (cons n (evaluate n c)
        (evaluate n (xs.foldr (fun h t => Nat.pair (h + 1) t) (atomCode 0)))).2 = _
      simp only [cons]
      rw [ih]
      rfl

/-- The outer rule tag consumes a checked proper list of interpreted
fields; scalar and recursive fields still have their different shapes. -/
theorem normalizeRule_node (n tag : ℕ) (xs : List ℕ) :
    normalizeRule n (nodeCode tag xs) =
      interpret n ruleSchemas (some tag)
        (some (xs.map fun c => (evaluate n c).1)) := by
  unfold normalizeRule nodeCode
  simp only [evaluate, PrimitiveSExpression.fold_cons]
  change (cons n (evaluate n (atomCode tag))
    (evaluate n (xs.foldr (fun h t => Nat.pair (h + 1) t) (atomCode 0)))).1.2.1 = _
  change interpret n _ (evaluate n (atomCode tag)).1.1
    (evaluate n (xs.foldr (fun h t => Nat.pair (h + 1) t) (atomCode 0))).2 = _
  rw [evaluate_fields]
  have ha : evaluate n (atomCode tag) = atom n tag := by
    exact PrimitiveSExpression.fold_atom atom cons n tag
  rw [ha]
  rfl

/-- The chain tag uses the same proper-list grammar and recursive tree fold. -/
theorem normalizeChain_node (n tag : ℕ) (xs : List ℕ) :
    normalizeChain n (nodeCode tag xs) =
      interpret n chainSchemas (some tag)
        (some (xs.map fun c => (evaluate n c).1)) := by
  unfold normalizeChain nodeCode
  simp only [evaluate, PrimitiveSExpression.fold_cons]
  change (cons n (evaluate n (atomCode tag))
    (evaluate n (xs.foldr (fun h t => Nat.pair (h + 1) t) (atomCode 0)))).1.2.2 = _
  change interpret n _ (evaluate n (atomCode tag)).1.1
    (evaluate n (xs.foldr (fun h t => Nat.pair (h + 1) t) (atomCode 0))).2 = _
  rw [evaluate_fields]
  have ha : evaluate n (atomCode tag) = atom n tag := by
    exact PrimitiveSExpression.fold_atom atom cons n tag
  rw [ha]
  rfl

@[simp] theorem normalizeRule_atom (n x : ℕ) :
    normalizeRule n (atomCode x) = none := by
  simp [normalizeRule, evaluate, atomCode, atom]

@[simp] theorem normalizeChain_atom (n x : ℕ) :
    normalizeChain n (atomCode x) = none := by
  simp [normalizeChain, evaluate, atomCode, atom]

section OriginalCodec

open private S S.nat S.cons S.encode S.decode S_equiv
  from Mathlib.Tactic.DeriveEncodable

-- Open the pinned derived mutual codec names after removing hygiene scopes.
-- This only introduces name aliases; every proof still uses existing constants.
run_cmd do
  let env ← Lean.getEnv
  let wanted : List (Lean.Name × String) :=
    [(`derivedRule, "instEncodableRuleCertificate.encodable_1_fromS"),
     (`derivedChain, "instEncodableRuleCertificate.encodable_2_fromS")]
  for (aliasName, suffix) in wanted do
    let auxiliaryNames := env.constants.toList.filter fun (name, _) =>
      name.eraseMacroScopes.toString.endsWith suffix
    let [(name, _)] := auxiliaryNames | throwError "expected unique original auxiliary {suffix}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit aliasName name :: scope.openDecls }


-- Open the pinned derived mutual codec names after removing hygiene scopes.
-- This only introduces name aliases; every proof still uses existing constants.
run_cmd do
  let env ← Lean.getEnv
  let wanted : List (Lean.Name × Lean.Name × String) :=
    [(`derivedRuleToS, `derivedRuleToSEq, "instEncodableRuleCertificate.encodable_1_toS"),
     (`derivedChainToS, `derivedChainToSEq, "instEncodableRuleCertificate.encodable_2_toS")]
  for (aliasName, equationAlias, suffix) in wanted do
    let auxiliaryNames := env.constants.toList.filter fun (name, _) =>
      name.eraseMacroScopes.toString.endsWith suffix
    let [(name, _)] := auxiliaryNames | throwError "expected unique original auxiliary {suffix}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit aliasName name :: scope.openDecls }
    let equationName := Lean.Name.str name "eq_def"
    Lean.Elab.Command.liftCoreM (Lean.executeReservedNameAction equationName)
    unless (← Lean.getEnv).contains equationName do
      throwError "original equation theorem not found: {equationName}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit equationAlias equationName :: scope.openDecls }


private theorem encodeRule_toS {n : ℕ} (r : RuleCertificate n) :
    encode r = S.encode (@derivedRuleToS n r) := rfl

private theorem encodeChain_toS {n : ℕ} (c : ChainCertificate n) :
    encode c = S.encode (@derivedChainToS n c) := rfl

theorem encode_arithmetic {n : ℕ} (P Q : PatternCode n) :
    encode (RuleCertificate.arithmetic P Q) =
      nodeCode 0 [atomCode (encode P), atomCode (encode Q)] := by
  rw [encodeRule_toS, derivedRuleToSEq]
  simp only [S.encode, nodeCode, atomCode, List.foldr_cons, List.foldr_nil]

theorem encode_refl {n : ℕ} (P : PatternCode n) :
    encode (ChainCertificate.refl P) = nodeCode 0 [atomCode (encode P)] := by
  rw [encodeChain_toS, derivedChainToSEq]
  simp only [S.encode, nodeCode, atomCode, List.foldr_cons, List.foldr_nil]

theorem encode_downward {n : ℕ} (P : PatternCode n) (k : Lvl)
    (a b : Fin n) (X N : Finset (Fin n)) (g : Fin n → Fin n) :
    encode (RuleCertificate.downward P k a b X N g) =
      nodeCode 1 [atomCode (encode P), atomCode (encode k), atomCode (encode a),
        atomCode (encode b), atomCode (encode X), atomCode (encode N), atomCode (encode g)] := by
  rw [encodeRule_toS, derivedRuleToSEq]
  simp only [S.encode, nodeCode, atomCode, List.foldr_cons, List.foldr_nil]

theorem encode_upward {n : ℕ} (r : RuleCertificate n)
    (a b : Fin n) (N : Finset (Fin n)) (g : Fin n → Fin n) :
    encode (RuleCertificate.upward r a b N g) =
      nodeCode 2 [encode r, atomCode (encode a), atomCode (encode b),
        atomCode (encode N), atomCode (encode g)] := by
  rw [encodeRule_toS, derivedRuleToSEq]
  simp only [S.encode, nodeCode, atomCode, List.foldr_cons, List.foldr_nil,
    ← encodeRule_toS]

theorem encode_finiteRestriction {n : ℕ} (c : ChainCertificate n)
    (Q : PatternCode n) (a : Fin n) :
    encode (RuleCertificate.finiteRestriction c Q a) =
      nodeCode 3 [encode c, atomCode (encode Q), atomCode (encode a)] := by
  rw [encodeRule_toS, derivedRuleToSEq]
  simp only [S.encode, nodeCode, atomCode, List.foldr_cons, List.foldr_nil,
    ← encodeChain_toS]

theorem encode_lifting {n : ℕ} (r : RuleCertificate n)
    (Q Qplus : PatternCode n) (h f : Fin n → Fin n) :
    encode (RuleCertificate.lifting r Q Qplus h f) =
      nodeCode 4 [encode r, atomCode (encode Q), atomCode (encode Qplus),
        atomCode (encode h), atomCode (encode f)] := by
  rw [encodeRule_toS, derivedRuleToSEq]
  simp only [S.encode, nodeCode, atomCode, List.foldr_cons, List.foldr_nil,
    ← encodeRule_toS]

theorem encode_tail {n : ℕ} (c : ChainCertificate n) (r : RuleCertificate n) :
    encode (ChainCertificate.tail c r) = nodeCode 1 [encode c, encode r] := by
  rw [encodeChain_toS, derivedChainToSEq]
  simp only [S.encode, nodeCode, atomCode, List.foldr_cons, List.foldr_nil,
    ← encodeChain_toS, ← encodeRule_toS]


private def lvlFrom : S → Option Lvl
  | S.cons (S.nat 0) (S.nat 0) => some .one
  | S.cons (S.nat 1) (S.nat 0) => some .two
  | _ => none

private theorem decodeLevel (code : ℕ) :
    (decode (α := Lvl) code).map encode =
      if code = 2 ∨ code = 6 then some code else none := by
  have hs (s : S) : (lvlFrom s).map encode =
      if S.encode s = 2 ∨ S.encode s = 6 then some (S.encode s) else none := by
    have h1 : S.encode s = 2 ↔ s = S.cons (S.nat 0) (S.nat 0) := by
      change S_equiv s = S_equiv (S.cons (S.nat 0) (S.nat 0)) ↔ _
      exact S_equiv.injective.eq_iff
    have h2 : S.encode s = 6 ↔ s = S.cons (S.nat 1) (S.nat 0) := by
      change S_equiv s = S_equiv (S.cons (S.nat 1) (S.nat 0)) ↔ _
      exact S_equiv.injective.eq_iff
    by_cases h : s = S.cons (S.nat 0) (S.nat 0)
    · subst s; rfl
    by_cases h' : s = S.cons (S.nat 1) (S.nat 0)
    · subst s; rfl
    have hc1 : S.encode s ≠ 2 := fun hc => h (h1.mp hc)
    have hc2 : S.encode s ≠ 6 := fun hc => h' (h2.mp hc)
    simp only [hc1, hc2, or_self, ↓reduceIte]
    cases s with
    | nat n => rfl
    | cons a b => cases a with
      | cons a b => rfl
      | nat n => cases n with
        | zero => cases b <;> simp_all [lvlFrom]
        | succ n => cases n with
          | zero => cases b <;> simp_all [lvlFrom]
          | succ n => rfl
  have hd : decode (α := Lvl) code = lvlFrom (S.decode code) := rfl
  rw [hd, hs, show S.encode (S.decode code) = code from S_equiv.right_inv code]

mutual

private def fromRule (n : ℕ) : S → Option (RuleCertificate n)
  | S.cons (S.nat 0) (S.cons (S.nat p) (S.cons (S.nat q) (S.nat 0))) =>
      match decode p, decode q with
      | some P, some Q => some (.arithmetic P Q)
      | _, _ => none
  | S.cons (S.nat 1) (S.cons (S.nat p) (S.cons (S.nat k)
      (S.cons (S.nat a) (S.cons (S.nat b) (S.cons (S.nat x)
      (S.cons (S.nat z) (S.cons (S.nat g) (S.nat 0)))))))) =>
      match decode p, decode k, decode a, decode b, decode x, decode z, decode g with
      | some P, some k, some a, some b, some X, some N, some g =>
          some (.downward P k a b X N g)
      | _, _, _, _, _, _, _ => none
  | S.cons (S.nat 2) (S.cons d (S.cons (S.nat a) (S.cons (S.nat b)
      (S.cons (S.nat z) (S.cons (S.nat g) (S.nat 0)))))) =>
      match fromRule n d, decode a, decode b, decode z, decode g with
      | some d, some a, some b, some N, some g => some (.upward d a b N g)
      | _, _, _, _, _ => none
  | S.cons (S.nat 3) (S.cons c (S.cons (S.nat q) (S.cons (S.nat a) (S.nat 0)))) =>
      match fromChain n c, decode q, decode a with
      | some c, some Q, some a => some (.finiteRestriction c Q a)
      | _, _, _ => none
  | S.cons (S.nat 4) (S.cons d (S.cons (S.nat q) (S.cons (S.nat r)
      (S.cons (S.nat h) (S.cons (S.nat f) (S.nat 0)))))) =>
      match fromRule n d, decode q, decode r, decode h, decode f with
      | some d, some Q, some R, some h, some f => some (.lifting d Q R h f)
      | _, _, _, _, _ => none
  | _ => none

private def fromChain (n : ℕ) : S → Option (ChainCertificate n)
  | S.cons (S.nat 0) (S.cons (S.nat p) (S.nat 0)) =>
      match decode p with
      | some P => some (.refl P)
      | _ => none
  | S.cons (S.nat 1) (S.cons c (S.cons d (S.nat 0))) =>
      match fromChain n c, fromRule n d with
      | some c, some d => some (.tail c d)
      | _, _ => none
  | _ => none

end

private theorem decodeRule_fromS (n code : ℕ) :
    decode (α := RuleCertificate n) code = fromRule n (S.decode code) := by
  change @derivedRule n (S.decode code) = _
  delta derivedRule fromRule
  congr 2

private theorem decodeChain_fromS (n code : ℕ) :
    decode (α := ChainCertificate n) code = fromChain n (S.decode code) := by
  change @derivedChain n (S.decode code) = _
  delta derivedChain fromChain
  congr 2

private def atomOf : S → Option ℕ
  | S.nat x => some x
  | S.cons _ _ => none

private def entry (n : ℕ) (s : S) : Entry :=
  (atomOf s, (fromRule n s).map encode, (fromChain n s).map encode)

private def spine (n : ℕ) : S → Option (List Entry)
  | S.nat x => if x = 0 then some [] else none
  | S.cons h t => (spine n t).map (entry n h :: ·)

private def scalar (α : Type*) [Encodable α] (s : S) : Option α :=
  (atomOf s).bind decode

private theorem field_pattern (n : ℕ) (s : S) :
    field n 0 (entry n s) = (scalar (PatternCode n) s).map (atomCode ∘ encode) := by
  cases s <;> simp [field, entry, atomOf, scalar, normalize_eq, Option.map_map]

private theorem field_level (n : ℕ) (s : S) :
    field n 1 (entry n s) = (scalar Lvl s).map (atomCode ∘ encode) := by
  cases s <;> simp [field, entry, atomOf, scalar, ← decodeLevel, Option.map_map]

private theorem field_label (n : ℕ) (s : S) :
    field n 2 (entry n s) = (scalar (Fin n) s).map (atomCode ∘ encode) := by
  cases s <;> simp [field, entry, atomOf, scalar, decodeLabel_eq, Option.map_map]
  rfl

private theorem field_carrier (n : ℕ) (s : S) :
    field n 3 (entry n s) =
      (scalar (Finset (Fin n)) s).map (atomCode ∘ encode) := by
  cases s <;> simp [field, entry, atomOf, scalar, decodeCarrier_eq, Option.map_map,
    encode_carrierView, Function.comp_def]

private theorem field_map (n : ℕ) (s : S) :
    field n 4 (entry n s) =
      (scalar (Fin n → Fin n) s).map (atomCode ∘ encode) := by
  have hd : decodeLabel n = fun c => (decode (α := Fin n) c).map encode := by
    funext c
    rw [decodeLabel_eq]
    rfl
  cases s <;> simp [field, entry, atomOf, scalar, hd, normalizeArrowWith_eq,
    Option.map_map]

private theorem field_rule (n : ℕ) (s : S) :
    field n 5 (entry n s) = (fromRule n s).map encode := rfl

private theorem field_chain (n : ℕ) (s : S) :
    field n 6 (entry n s) = (fromChain n s).map encode := rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2400000 in
private theorem rule_cons (n : ℕ) (h t : S) :
    interpret n ruleSchemas (atomOf h) (spine n t) =
      (fromRule n (S.cons h t)).map encode := by
  rw [fromRule.eq_def]
  cases h with
  | cons a b => simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
  | nat tag =>
    cases tag with
    | zero =>
        cases t with
        | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
        | cons p t1 =>
            cases p with
            | cons badH badT =>
                cases hs : spine n t1 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
            | nat p =>
                cases t1 with
                | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                | cons q t2 =>
                    cases q with
                    | cons badH badT =>
                        cases hs : spine n t2 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                    | nat q =>
                        cases t2 with
                        | cons extra rest =>
                            cases hs : spine n rest <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                        | nat z =>
                            cases z with
                            | succ z => simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                            | zero =>
                                simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                cases h0 : decode (α := PatternCode n) p <;> simp only [h0, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                cases h1 : decode (α := PatternCode n) q <;> simp only [h1, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                all_goals simp only [encode_arithmetic, encode_refl, encode_downward, encode_upward,
                                  encode_finiteRestriction, encode_lifting, encode_tail]
    | succ tag =>
        cases tag with
        | zero =>
            cases t with
            | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
            | cons p t1 =>
                cases p with
                | cons badH badT =>
                    cases hs : spine n t1 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                | nat p =>
                    cases t1 with
                    | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                    | cons k t2 =>
                        cases k with
                        | cons badH badT =>
                            cases hs : spine n t2 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                        | nat k =>
                            cases t2 with
                            | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                            | cons a t3 =>
                                cases a with
                                | cons badH badT =>
                                    cases hs : spine n t3 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                | nat a =>
                                    cases t3 with
                                    | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                    | cons b t4 =>
                                        cases b with
                                        | cons badH badT =>
                                            cases hs : spine n t4 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                        | nat b =>
                                            cases t4 with
                                            | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                            | cons x t5 =>
                                                cases x with
                                                | cons badH badT =>
                                                    cases hs : spine n t5 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                | nat x =>
                                                    cases t5 with
                                                    | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                    | cons z t6 =>
                                                        cases z with
                                                        | cons badH badT =>
                                                            cases hs : spine n t6 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                        | nat z =>
                                                            cases t6 with
                                                            | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                            | cons g t7 =>
                                                                cases g with
                                                                | cons badH badT =>
                                                                    cases hs : spine n t7 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                                | nat g =>
                                                                    cases t7 with
                                                                    | cons extra rest =>
                                                                        cases hs : spine n rest <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                                    | nat z =>
                                                                        cases z with
                                                                        | succ z => simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                                        | zero =>
                                                                            simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                                            cases h0 : decode (α := PatternCode n) p <;> simp only [h0, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                                            cases h1 : decode (α := Lvl) k <;> simp only [h1, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                                            cases h2 : decode (α := Fin n) a <;> simp only [h2, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                                            cases h3 : decode (α := Fin n) b <;> simp only [h3, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                                            cases h4 : decode (α := Finset (Fin n)) x <;> simp only [h4, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                                            cases h5 : decode (α := Finset (Fin n)) z <;> simp only [h5, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                                            cases h6 : decode (α := Fin n → Fin n) g <;> simp only [h6, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                                            all_goals simp only [encode_arithmetic, encode_refl, encode_downward, encode_upward,
                                                                              encode_finiteRestriction, encode_lifting, encode_tail]
        | succ tag =>
            cases tag with
            | zero =>
                cases t with
                | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                | cons dR t1 =>
                    cases t1 with
                    | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                    | cons a t2 =>
                        cases a with
                        | cons badH badT =>
                            cases hs : spine n t2 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                        | nat a =>
                            cases t2 with
                            | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                            | cons b t3 =>
                                cases b with
                                | cons badH badT =>
                                    cases hs : spine n t3 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                | nat b =>
                                    cases t3 with
                                    | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                    | cons z t4 =>
                                        cases z with
                                        | cons badH badT =>
                                            cases hs : spine n t4 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                        | nat z =>
                                            cases t4 with
                                            | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                            | cons g t5 =>
                                                cases g with
                                                | cons badH badT =>
                                                    cases hs : spine n t5 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                | nat g =>
                                                    cases t5 with
                                                    | cons extra rest =>
                                                        cases hs : spine n rest <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                    | nat z =>
                                                        cases z with
                                                        | succ z => simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                        | zero =>
                                                            simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                            cases h0 : fromRule n dR <;> simp only [h0, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                            cases h1 : decode (α := Fin n) a <;> simp only [h1, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                            cases h2 : decode (α := Fin n) b <;> simp only [h2, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                            cases h3 : decode (α := Finset (Fin n)) z <;> simp only [h3, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                            cases h4 : decode (α := Fin n → Fin n) g <;> simp only [h4, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                            all_goals simp only [encode_arithmetic, encode_refl, encode_downward, encode_upward,
                                                              encode_finiteRestriction, encode_lifting, encode_tail]
            | succ tag =>
                cases tag with
                | zero =>
                    cases t with
                    | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                    | cons cC t1 =>
                        cases t1 with
                        | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                        | cons q t2 =>
                            cases q with
                            | cons badH badT =>
                                cases hs : spine n t2 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                            | nat q =>
                                cases t2 with
                                | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                | cons a t3 =>
                                    cases a with
                                    | cons badH badT =>
                                        cases hs : spine n t3 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                    | nat a =>
                                        cases t3 with
                                        | cons extra rest =>
                                            cases hs : spine n rest <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                        | nat z =>
                                            cases z with
                                            | succ z => simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                            | zero =>
                                                simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                cases h0 : fromChain n cC <;> simp only [h0, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                cases h1 : decode (α := PatternCode n) q <;> simp only [h1, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                cases h2 : decode (α := Fin n) a <;> simp only [h2, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                all_goals simp only [encode_arithmetic, encode_refl, encode_downward, encode_upward,
                                                  encode_finiteRestriction, encode_lifting, encode_tail]
                | succ tag =>
                    cases tag with
                    | zero =>
                        cases t with
                        | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                        | cons dR t1 =>
                            cases t1 with
                            | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                            | cons q t2 =>
                                cases q with
                                | cons badH badT =>
                                    cases hs : spine n t2 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                | nat q =>
                                    cases t2 with
                                    | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                    | cons r t3 =>
                                        cases r with
                                        | cons badH badT =>
                                            cases hs : spine n t3 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                        | nat r =>
                                            cases t3 with
                                            | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                            | cons h t4 =>
                                                cases h with
                                                | cons badH badT =>
                                                    cases hs : spine n t4 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                | nat h =>
                                                    cases t4 with
                                                    | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                    | cons f t5 =>
                                                        cases f with
                                                        | cons badH badT =>
                                                            cases hs : spine n t5 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                        | nat f =>
                                                            cases t5 with
                                                            | cons extra rest =>
                                                                cases hs : spine n rest <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                            | nat z =>
                                                                cases z with
                                                                | succ z => simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                                | zero =>
                                                                    simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                                                                    cases h0 : fromRule n dR <;> simp only [h0, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                                    cases h1 : decode (α := PatternCode n) q <;> simp only [h1, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                                    cases h2 : decode (α := PatternCode n) r <;> simp only [h2, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                                    cases h3 : decode (α := Fin n → Fin n) h <;> simp only [h3, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                                    cases h4 : decode (α := Fin n → Fin n) f <;> simp only [h4, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                                                                    all_goals simp only [encode_arithmetic, encode_refl, encode_downward, encode_upward,
                                                                      encode_finiteRestriction, encode_lifting, encode_tail]
                    | succ tag =>
                        simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
private theorem chain_cons (n : ℕ) (h t : S) :
    interpret n chainSchemas (atomOf h) (spine n t) =
      (fromChain n (S.cons h t)).map encode := by
  rw [fromChain.eq_def]
  cases h with
  | cons a b => simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
  | nat tag =>
    cases tag with
    | zero =>
        cases t with
        | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
        | cons p t1 =>
            cases p with
            | cons badH badT =>
                cases hs : spine n t1 <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
            | nat p =>
                cases t1 with
                | cons extra rest =>
                    cases hs : spine n rest <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                | nat z =>
                    cases z with
                    | succ z => simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                    | zero =>
                        simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                        cases h0 : decode (α := PatternCode n) p <;> simp only [h0, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                        all_goals simp only [encode_arithmetic, encode_refl, encode_downward, encode_upward,
                          encode_finiteRestriction, encode_lifting, encode_tail]
    | succ tag =>
        cases tag with
        | zero =>
            cases t with
            | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
            | cons cC t1 =>
                cases t1 with
                | nat z => cases z <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                | cons dR t2 =>
                    cases t2 with
                    | cons extra rest =>
                        cases hs : spine n rest <;> simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                    | nat z =>
                        cases z with
                        | succ z => simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                        | zero =>
                            simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]
                            cases h0 : fromChain n cC <;> simp only [h0, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                            cases h1 : fromRule n dR <;> simp only [h1, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none]
                            all_goals simp only [encode_arithmetic, encode_refl, encode_downward, encode_upward,
                              encode_finiteRestriction, encode_lifting, encode_tail]
        | succ tag =>
            simp [interpret, ruleSchemas, chainSchemas, spine, atomOf, fields_nil, fields_emptyargs, fields_cons, field_pattern, field_level, field_label, field_carrier, field_map, field_rule, field_chain, scalar, Option.map_map, Function.comp_def]


private theorem evaluate_encode (n : ℕ) (s : S) :
    evaluate n (S.encode s) = (entry n s, spine n s) := by
  induction s with
  | nat x =>
      simp [evaluate, S.encode, PrimitiveSExpression.fold_atom, atom, entry,
        atomOf, fromRule, fromChain, spine]
  | cons h t ihh iht =>
      change PrimitiveSExpression.fold atom cons n
        (Nat.pair (S.encode h + 1) (S.encode t)) = _
      rw [PrimitiveSExpression.fold_cons]
      change cons n (evaluate n (S.encode h)) (evaluate n (S.encode t)) = _
      rw [ihh, iht]
      change ((none, interpret n ruleSchemas (atomOf h) (spine n t),
        interpret n chainSchemas (atomOf h) (spine n t)),
        (spine n t).map (entry n h :: ·)) = _
      rw [rule_cons, chain_cons]
      rfl

/-- Exact normalization of the original mutual rule decoder on every raw
input, uniformly in the finite label bound. -/
theorem normalizeRule_eq (n code : ℕ) :
    normalizeRule n code = (decode (α := RuleCertificate n) code).map encode := by
  rw [decodeRule_fromS]
  have h := evaluate_encode n (S.decode code)
  rw [show S.encode (S.decode code) = code from S_equiv.right_inv code] at h
  simp only [normalizeRule, h, entry]

/-- Exact normalization of the original mutual chain decoder, including
malformed recursive children and scalar fields. -/
theorem normalizeChain_eq (n code : ℕ) :
    normalizeChain n code = (decode (α := ChainCertificate n) code).map encode := by
  rw [decodeChain_fromS]
  have h := evaluate_encode n (S.decode code)
  rw [show S.encode (S.decode code) = code from S_equiv.right_inv code] at h
  simp only [normalizeChain, h, entry]

end OriginalCodec

/-- Erasing the decoded rule to its code preserves its original encoded
`Option` result, including rejection. -/
theorem encode_normalizeRule (n code : ℕ) :
    encode (normalizeRule n code) = encode (decode (α := RuleCertificate n) code) := by
  rw [normalizeRule_eq]
  cases decode (α := RuleCertificate n) code <;> rfl

/-- The same compatibility for chains. -/
theorem encode_normalizeChain (n code : ℕ) :
    encode (normalizeChain n code) = encode (decode (α := ChainCertificate n) code) := by
  rw [normalizeChain_eq]
  cases decode (α := ChainCertificate n) code <;> rfl

theorem encoded_rule_decode_primrec (n : ℕ) :
    Primrec (fun c : ℕ => encode (decode (α := RuleCertificate n) c)) :=
  (Primrec.encode.comp (normalizeRule_primrec.comp (Primrec.const n) Primrec.id)).of_eq
    (encode_normalizeRule n)

theorem encoded_chain_decode_primrec (n : ℕ) :
    Primrec (fun c : ℕ => encode (decode (α := ChainCertificate n) c)) :=
  (Primrec.encode.comp (normalizeChain_primrec.comp (Primrec.const n) Primrec.id)).of_eq
    (encode_normalizeChain n)

/-- The original derived rule coding, now certified primitive recursive. -/
instance instPrimcodableRuleCertificate (n : ℕ) : Primcodable (RuleCertificate n) where
  toEncodable := @instEncodableRuleCertificate n
  prim := Primrec.nat_iff.mp (encoded_rule_decode_primrec n)

/-- The original derived chain coding, with no encoding replacement. -/
instance instPrimcodableChainCertificate (n : ℕ) : Primcodable (ChainCertificate n) where
  toEncodable := @instEncodableChainCertificate n
  prim := Primrec.nat_iff.mp (encoded_chain_decode_primrec n)

@[simp] theorem rule_encoding_unchanged (n : ℕ) :
    (instPrimcodableRuleCertificate n).toEncodable = @instEncodableRuleCertificate n := rfl

@[simp] theorem chain_encoding_unchanged (n : ℕ) :
    (instPrimcodableChainCertificate n).toEncodable = @instEncodableChainCertificate n := rfl

@[simp] theorem normalizeRule_encode {n : ℕ} (d : RuleCertificate n) :
    normalizeRule n (encode d) = some (encode d) := by
  rw [normalizeRule_eq, Encodable.encodek]
  rfl

@[simp] theorem normalizeChain_encode {n : ℕ} (d : ChainCertificate n) :
    normalizeChain n (encode d) = some (encode d) := by
  rw [normalizeChain_eq, Encodable.encodek]
  rfl

/-- One actual total mathlib machine normalizes all finite rule codes. -/
theorem rule_normalize_program : ∃ c : Nat.Partrec.Code, ∀ n code : ℕ,
    c.eval (Nat.pair n code) = Part.some (encode (normalizeRule n code)) := by
  obtain ⟨c, hc⟩ := PrimitiveRationalPresentation.exists_code normalizeRule_primrec
  exact ⟨c, fun n code => hc (n, code)⟩

/-- One actual total mathlib machine normalizes all finite chain codes. -/
theorem chain_normalize_program : ∃ c : Nat.Partrec.Code, ∀ n code : ℕ,
    c.eval (Nat.pair n code) = Part.some (encode (normalizeChain n code)) := by
  obtain ⟨c, hc⟩ := PrimitiveRationalPresentation.exists_code normalizeChain_primrec
  exact ⟨c, fun n code => hc (n, code)⟩



end Alexander313.Carlson.PrimitiveRecursiveCertificates
