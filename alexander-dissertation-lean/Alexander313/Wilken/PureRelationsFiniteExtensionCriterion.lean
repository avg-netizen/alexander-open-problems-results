import Alexander313.Wilken.PureRelationsReflectionConverse

/-!
# Genuine second elementarity from the complete finite-extension criterion

This is the sufficient criterion of source Proposition1.6(2), written on a
whole original finite set. One lower copy fixes every original lower point
and preserves ALL positive and negative expanded facts. Every finite lower
extension of that copy can be mapped back into the original upper segment,
with the whole original copy sent back pointwise. This constructs actual
Sigma2 elementarity: each lower universal tuple belongs to ONE finite
extension, whose actual full pattern transports the matrix truth.

The extension property is the printed mathematical premise of the criterion,
not an assumed relation decision or elementarity theorem. No converse from
actual R2 to that property, public recursive decision or guard room is claimed.
These candidates stay outside the package checkpoint until review.
-/

noncomputable section

namespace Alexander313.Wilken.PureRelations

/-- A whole-set version of the printed finite extension property. The map
back on an extension agrees with the inverse of the ORIGINAL finite copy. -/
def FiniteExtensionReflection (α β : Ordinal.{0}) : Prop :=
  ∀ F : Finset Ordinal.{0}, (∀ x ∈ F, x < β) →
    ∃ f : Ordinal.{0} → Ordinal.{0}, (∀ x ∈ F, f x < α) ∧
      (∀ x ∈ F, x < α → f x = x) ∧ PreservesPattern F f ∧
      ∀ G : Finset Ordinal.{0}, (∀ x ∈ G, x < α) →
        (∀ x ∈ F, f x ∈ G) →
        ∃ g : Ordinal.{0} → Ordinal.{0}, (∀ x ∈ G, g x < β) ∧
          (∀ x ∈ F, g (f x) = x) ∧ PreservesPattern G g

theorem finiteExtensionReflection_finiteReflection (α β : Ordinal.{0})
    (extension : FiniteExtensionReflection α β) : FiniteReflection α β := by
  intro F hF
  obtain ⟨f, lower, fixed, pattern, _⟩ := extension F hF
  exact ⟨f, lower, fixed, pattern⟩

/-- A genuine upper existential-universal witness yields a SINGLE lower
existential witness. Every lower universal tuple is handled by a finite
extension containing that witness AND every original parameter. -/
theorem finiteExtensionReflection_sigma2_reflects (α β : Ordinal.{0})
    (hαβ : α ≤ β) (extension : FiniteExtensionReflection α β)
    (p m n : Nat) (φ : Matrix ((p + m) + n)) (v : Fin p → Ordinal.{0})
    (hv : TupleBelow α v) :
    sigma2Truth R1 R2 β p m n φ v → sigma2Truth R1 R2 α p m n φ v := by
  classical
  rintro ⟨w, hw, truth⟩
  let F : Finset Ordinal.{0} := (List.ofFn v).toFinset ∪ (List.ofFn w).toFinset
  have vmem (i : Fin p) : v i ∈ F := Finset.mem_union.mpr
    (Or.inl (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)))
  have wmem (i : Fin m) : w i ∈ F := Finset.mem_union.mpr
    (Or.inr (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)))
  have belowF : ∀ x ∈ F, x < β := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hx)
      exact (hv i).trans_le hαβ
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hx)
      exact hw i
  obtain ⟨f, lower, fixed, _, extend⟩ := extension F belowF
  let w' : Fin m → Ordinal.{0} := fun i => f (w i)
  refine ⟨w', fun i => lower (w i) (wmem i), ?_⟩
  intro z hz
  let G : Finset Ordinal.{0} := F.image f ∪ (List.ofFn z).toFinset
  have copied (x : Ordinal.{0}) (hx : x ∈ F) : f x ∈ G :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  have zmem (i : Fin n) : z i ∈ G := Finset.mem_union.mpr
    (Or.inr (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)))
  have belowG : ∀ x ∈ G, x < α := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact lower y hy
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hx)
      exact hz i
  obtain ⟨g, upper, back, pattern⟩ := extend G belowG copied
  have gvmem (i : Fin p) : v i ∈ G := by
    simpa only [fixed (v i) (vmem i) (hv i)] using copied (v i) (vmem i)
  have gv (i : Fin p) : g (v i) = v i := by
    simpa only [fixed (v i) (vmem i) (hv i)] using back (v i) (vmem i)
  have gw (i : Fin m) : g (w' i) = w i := back (w i) (wmem i)
  have hmem : ∀ i, Fin.append (Fin.append v w') z i ∈ G := by
    apply (Fin.forall_fin_add
      (fun i => Fin.append (Fin.append v w') z i ∈ G)).mpr
    constructor
    · simp only [Fin.append_left]
      apply (Fin.forall_fin_add (fun i => Fin.append v w' i ∈ G)).mpr
      constructor
      · intro i
        simpa only [Fin.append_left] using gvmem i
      · intro i
        simpa only [Fin.append_right, w'] using copied (w i) (wmem i)
    · intro i
      simpa only [Fin.append_right] using zmem i
  have mapped : (fun i => g (Fin.append (Fin.append v w') z i)) =
      Fin.append (Fin.append v w) (fun i => g (z i)) := by
    apply funext
    apply (Fin.forall_fin_add
      (fun i => g (Fin.append (Fin.append v w') z i) =
        Fin.append (Fin.append v w) (fun i => g (z i)) i)).mpr
    constructor
    · simp only [Fin.append_left]
      apply (Fin.forall_fin_add
        (fun i => g (Fin.append v w' i) = Fin.append v w i)).mpr
      constructor
      · intro i
        simpa only [Fin.append_left] using gv i
      · intro i
        simpa only [Fin.append_right] using gw i
    · intro i
      simp only [Fin.append_right]
  apply (matrix_realize_pattern φ G g pattern (Fin.append (Fin.append v w') z) hmem).mp
  rw [mapped]
  exact truth (fun i => g (z i)) (fun i => upper (z i) (zmem i))

theorem finiteExtensionReflection_sigma2Elementary (α β : Ordinal.{0})
    (hαβ : α ≤ β) (extension : FiniteExtensionReflection α β) :
    Sigma2Elementary R1 R2 α β := by
  have first := finiteReflection_sigma1Elementary α β hαβ
    (finiteExtensionReflection_finiteReflection α β extension)
  intro p m n φ v hv
  exact ⟨sigma2Truth_mono_of_sigma1 R1 R2 α β hαβ first p m n φ v hv,
    finiteExtensionReflection_sigma2_reflects α β hαβ extension p m n φ v hv⟩

/-- The sufficient criterion of Proposition1.6(2) concludes the ACTUAL
recursively constructed second relation; no elementarity is an input. -/
theorem R2_of_finiteExtensionReflection (α β : Ordinal.{0}) (hαβ : α ≤ β)
    (extension : FiniteExtensionReflection α β) : R2 α β :=
  (R2_actual_iff α β).mpr
    ⟨hαβ, finiteExtensionReflection_sigma2Elementary α β hαβ extension⟩

end Alexander313.Wilken.PureRelations
