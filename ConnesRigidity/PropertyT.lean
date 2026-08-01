


import ConnesRigidity.Groups
import Mathlib.Analysis.InnerProductSpace.Adjoint











namespace ConnesRigidity

universe u

namespace UnitaryRepresentation

variable {G H : Type u} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


def stabilizer (π : UnitaryRepresentation G H) (ξ : H) : Subgroup G where
  carrier := {g | (π g : H →L[ℂ] H) ξ = ξ}
  one_mem' := by
    simp
  mul_mem' := by
    intro g h hg hh
    change (π g : H →L[ℂ] H) ξ = ξ at hg
    change (π h : H →L[ℂ] H) ξ = ξ at hh
    simp [map_mul, hh, hg]
  inv_mem' := by
    intro g hg
    calc
      (π g⁻¹ : H →L[ℂ] H) ξ =
          (π g⁻¹ : H →L[ℂ] H) ((π g : H →L[ℂ] H) ξ) := by rw [hg]
      _ = ξ := by
        change (↑(π g⁻¹ * π g) : H →L[ℂ] H) ξ = ξ
        rw [← map_mul]
        simp

@[simp]
theorem mem_stabilizer_iff
    (π : UnitaryRepresentation G H) (ξ : H) (g : G) :
    g ∈ π.stabilizer ξ ↔ (π g : H →L[ℂ] H) ξ = ξ :=
  Iff.rfl

end UnitaryRepresentation


def IsGeneratingSet (G : Type u) [Group G] (K : Finset G) : Prop :=
  Subgroup.closure (K : Set G) = ⊤


theorem UnitaryRepresentation.isInvariant_of_isGeneratingSet
    {G H : Type u} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K : Finset G) (hK : IsGeneratingSet G K)
    (ξ : H) (hξ : ∀ g ∈ K, (π g : H →L[ℂ] H) ξ = ξ) :
    π.IsInvariant ξ := by
  have hsubset : (K : Set G) ⊆ π.stabilizer ξ := by
    intro g hg
    exact hξ g hg
  have hclosure : Subgroup.closure (K : Set G) ≤ π.stabilizer ξ :=
    (Subgroup.closure_le _).mpr hsubset
  rw [hK] at hclosure
  intro g
  exact hclosure (Subgroup.mem_top g)







def IsKazhdanPair
    (G : CountableDiscreteGroup.{u}) (K : Finset G) (ε : ℝ) : Prop :=
  0 < ε ∧
    ∀ (H : Type u)
      (_ : NormedAddCommGroup H)
      (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H)
      (π : UnitaryRepresentation G H)
      (ξ : H),
      ‖ξ‖ = 1 →
      (∀ g ∈ K, ‖(π g : H →L[ℂ] H) ξ - ξ‖ < ε) →
        ∃ η : H, η ≠ 0 ∧ π.IsInvariant η


theorem hasKazhdanPropertyT_of_isKazhdanPair
    (G : CountableDiscreteGroup.{u}) (K : Finset G) (ε : ℝ)
    (hK : IsKazhdanPair G K ε) :
    HasKazhdanPropertyT G := by
  intro H _ _ _ π hπ
  obtain ⟨ξ, hξ, hclose⟩ := hπ K ε hK.1
  exact hK.2 H inferInstance inferInstance inferInstance π ξ hξ hclose


theorem UnitaryRepresentation.hasAlmostInvariantUnitVectors_comp
    {G H K : Type u} [Group G] [Group H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : UnitaryRepresentation H K)
    (f : G →* H)
    (hπ : π.HasAlmostInvariantUnitVectors) :
    UnitaryRepresentation.HasAlmostInvariantUnitVectors (π.comp f) := by
  classical
  intro S ε hε
  obtain ⟨ξ, hξ, hclose⟩ := hπ (S.image f) ε hε
  refine ⟨ξ, hξ, ?_⟩
  intro g hg
  exact hclose (f g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)


theorem hasKazhdanPropertyT_of_surjective
    (G H : CountableDiscreteGroup.{u})
    (f : G →* H) (hf : Function.Surjective f)
    (hG : HasKazhdanPropertyT G) :
    HasKazhdanPropertyT H := by
  intro K _ _ _ π hπ
  obtain ⟨ξ, hξ, hinv⟩ :=
    hG K inferInstance inferInstance inferInstance (π.comp f)
      (UnitaryRepresentation.hasAlmostInvariantUnitVectors_comp π f hπ)
  refine ⟨ξ, hξ, ?_⟩
  intro h
  obtain ⟨g, rfl⟩ := hf h
  exact hinv g


theorem hasKazhdanPropertyT_iff_of_mulEquiv
    (G H : CountableDiscreteGroup.{u}) (e : G ≃* H) :
    HasKazhdanPropertyT G ↔ HasKazhdanPropertyT H := by
  constructor
  · exact hasKazhdanPropertyT_of_surjective G H e.toMonoidHom e.surjective
  · exact hasKazhdanPropertyT_of_surjective H G e.symm.toMonoidHom e.symm.surjective

end ConnesRigidity
