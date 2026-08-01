import Mathlib

attribute [instance 2000] InnerProductSpace.toInner ContinuousLinearMap.instStarModuleId

namespace ConnesRigidity

universe u v

structure CountableDiscreteGroup where
  Carrier : Type u
  group : Group Carrier
  countable : Countable Carrier

namespace CountableDiscreteGroup

instance : CoeSort CountableDiscreteGroup (Type u) :=
  ⟨CountableDiscreteGroup.Carrier⟩

attribute [instance] group countable

end CountableDiscreteGroup

def conjugacyClass (G : CountableDiscreteGroup) (g : G) : Set G :=
  {h | ∃ x : G, h = x * g * x⁻¹}

def IsICC (G : CountableDiscreteGroup) : Prop :=
  Infinite G ∧ ∀ g : G, g ≠ 1 → Set.Infinite (conjugacyClass G g)

def GroupsIsomorphic (G H : CountableDiscreteGroup) : Prop :=
  Nonempty (G ≃* H)

abbrev UnitaryRepresentation
    (G : Type u) [Group G]
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  G →* unitary (H →L[ℂ] H)

namespace UnitaryRepresentation

variable {G H : Type u} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def IsInvariant (π : UnitaryRepresentation G H) (ξ : H) : Prop :=
  ∀ g : G, (π g : H →L[ℂ] H) ξ = ξ

def HasAlmostInvariantUnitVectors (π : UnitaryRepresentation G H) : Prop :=
  ∀ (K : Finset G) (ε : ℝ), 0 < ε →
    ∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ g ∈ K, ‖(π g : H →L[ℂ] H) ξ - ξ‖ < ε

end UnitaryRepresentation

def HasKazhdanPropertyT (G : CountableDiscreteGroup.{u}) : Prop :=
  ∀ (H : Type u)
    (_ : NormedAddCommGroup H)
    (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H)
    (π : UnitaryRepresentation G H),
    π.HasAlmostInvariantUnitVectors →
      ∃ ξ : H, ξ ≠ 0 ∧ π.IsInvariant ξ

noncomputable section

open scoped NNReal ENNReal

abbrev GroupL2 (G : Type u) := lp (fun _ : G ↦ ℂ) 2

def l2ReindexFun {α : Type u} {β : Type v} (e : α ≃ β)
    (f : GroupL2 α) : PreLp (fun _ : β ↦ ℂ) :=
  fun j ↦ f (e.symm j)

theorem l2ReindexFun_mem {α : Type u} {β : Type v} (e : α ≃ β)
    (f : GroupL2 α) :
    l2ReindexFun e f ∈ lp (fun _ : β ↦ ℂ) 2 := by
  change Memℓp (fun j : β ↦ f (e.symm j)) 2
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  exact (e.symm.summable_iff).2
    ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))

def l2Reindex {α : Type u} {β : Type v} (e : α ≃ β) :
    GroupL2 α ≃ₗᵢ[ℂ] GroupL2 β where
  toLinearEquiv :=
    { toFun := fun f ↦ ⟨l2ReindexFun e f, l2ReindexFun_mem e f⟩
      invFun := fun f ↦ ⟨l2ReindexFun e.symm f, l2ReindexFun_mem e.symm f⟩
      left_inv := by
        intro f
        ext i
        change f (e.symm (e i)) = f i
        simp
      right_inv := by
        intro f
        ext j
        change f (e (e.symm j)) = f j
        simp
      map_add' := by
        intro f g
        ext j
        rfl
      map_smul' := by
        intro c f
        ext j
        rfl }
  norm_map' := by
    intro f
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    congr 1
    exact e.symm.tsum_eq (fun i ↦ ‖f i‖ ^ (2 : ℝ≥0∞).toReal)

@[simp]
theorem l2Reindex_apply {α : Type u} {β : Type v} (e : α ≃ β)
    (f : GroupL2 α) (j : β) :
    l2Reindex e f j = f (e.symm j) :=
  rfl

@[simp]
theorem l2Reindex_symm {α : Type u} {β : Type v} (e : α ≃ β) :
    (l2Reindex e).symm = l2Reindex e.symm := by
  ext f i
  rfl

def leftRegularUnitary {G : Type u} [Group G] (g : G) :
    unitary (GroupL2 G →L[ℂ] GroupL2 G) :=
  Unitary.linearIsometryEquiv.symm (l2Reindex (Equiv.mulLeft g))

@[simp]
theorem leftRegularUnitary_apply {G : Type u} [Group G]
    (g : G) (f : GroupL2 G) (h : G) :
    (leftRegularUnitary g : GroupL2 G →L[ℂ] GroupL2 G) f h = f (g⁻¹ * h) := by
  rfl

def leftRegularRepresentation (G : Type u) [Group G] :
    G →* unitary (GroupL2 G →L[ℂ] GroupL2 G) where
  toFun := leftRegularUnitary
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    ext h
    simp
  map_mul' g h := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    ext k
    simp [mul_assoc]

def vonNeumannClosure
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Set (H →L[ℂ] H)) :
    VonNeumannAlgebra H where
  toStarSubalgebra :=
    StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    change
      Set.centralizer
          (Set.centralizer
            ((StarSubalgebra.centralizer ℂ
              (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))) :
                Set (H →L[ℂ] H))) =
        ((StarSubalgebra.centralizer ℂ
          (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))) :
            Set (H →L[ℂ] H))
    rw [StarSubalgebra.coe_centralizer_centralizer]
    exact Set.centralizer_centralizer_centralizer ((S ∪ star S).centralizer)

def groupVonNeumannAlgebra (G : CountableDiscreteGroup.{u}) :
    VonNeumannAlgebra (GroupL2 G) :=
  vonNeumannClosure (Set.range fun g : G ↦
    (leftRegularRepresentation G g : GroupL2 G →L[ℂ] GroupL2 G))

abbrev GroupVonNeumannAlgebra (G : CountableDiscreteGroup.{u}) :=
  (groupVonNeumannAlgebra G).toStarSubalgebra

def delta (G : CountableDiscreteGroup.{u}) (g : G) : GroupL2 G :=
  by
    classical
    exact lp.single 2 g 1

def canonicalTrace (G : CountableDiscreteGroup.{u}) :
    GroupVonNeumannAlgebra G → ℂ :=
  fun x ↦ inner ℂ (delta G 1) ((x : GroupL2 G →L[ℂ] GroupL2 G) (delta G 1))

def ProjectionLE {A : Type u} [Mul A] (p q : A) : Prop :=
  p * q = p

def IsProjectionSupremum {A : Type u} [Mul A] [Star A]
    (S : Set A) (p : A) : Prop :=
  IsStarProjection p ∧
    (∀ q ∈ S, IsStarProjection q ∧ ProjectionLE q p) ∧
    ∀ r, IsStarProjection r → (∀ q ∈ S, ProjectionLE q r) → ProjectionLE p r

def IsNormalStarAlgEquiv
    {A : Type u} {B : Type v}
    [Semiring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) : Prop :=
  (∀ (S : Set A) (p : A), IsProjectionSupremum S p →
    IsProjectionSupremum (e '' S) (e p)) ∧
  ∀ (S : Set B) (p : B), IsProjectionSupremum S p →
    IsProjectionSupremum (e.symm '' S) (e.symm p)

structure TracialGroupFactorEquiv
    (G : CountableDiscreteGroup.{u}) (H : CountableDiscreteGroup.{v}) where
  toStarAlgEquiv :
    GroupVonNeumannAlgebra G ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra H
  normal : IsNormalStarAlgEquiv toStarAlgEquiv
  trace_preserving :
    ∀ x, canonicalTrace H (toStarAlgEquiv x) = canonicalTrace G x

def TracialGroupFactorsIsomorphic
    (G : CountableDiscreteGroup.{u}) (H : CountableDiscreteGroup.{v}) : Prop :=
  Nonempty (TracialGroupFactorEquiv G H)

end

def ConnesRigidityAssertion : Prop :=
  ∀ Γ Λ : CountableDiscreteGroup.{0},
    IsICC Γ →
    HasKazhdanPropertyT Γ →
    TracialGroupFactorsIsomorphic Γ Λ →
    IsICC Λ ∧ GroupsIsomorphic Γ Λ

theorem connesRigidityAssertion_false :
    ¬ConnesRigidityAssertion := by
  sorry

end ConnesRigidity
