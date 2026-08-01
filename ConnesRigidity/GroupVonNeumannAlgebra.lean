
import ConnesRigidity.Groups
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace ConnesRigidity

noncomputable section

open scoped NNReal ENNReal

universe u v

theorem isProjectionSupremum_image_starAlgEquiv
    {A : Type u} {B : Type v}
    [Semiring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) (S : Set A) (p : A)
    (hp : IsProjectionSupremum S p) :
    IsProjectionSupremum (e '' S) (e p) := by
  refine ⟨hp.1.map e, ?_, ?_⟩
  · rintro q ⟨r, hrS, rfl⟩
    exact ⟨(hp.2.1 r hrS).1.map e,
      by
        simpa [ProjectionLE] using
          congrArg e (hp.2.1 r hrS).2⟩
  · intro r hr hupper
    have hr' : IsStarProjection (e.symm r) := hr.map e.symm
    have hbound : ∀ q ∈ S, ProjectionLE q (e.symm r) := by
      intro q hq
      have himage : e q ∈ e '' S := ⟨q, hq, rfl⟩
      have h := hupper (e q) himage
      simpa [ProjectionLE] using congrArg e.symm h
    have hleast := hp.2.2 (e.symm r) hr' hbound
    simpa [ProjectionLE] using congrArg e hleast

theorem starAlgEquiv_isNormal
    {A : Type u} {B : Type v}
    [Semiring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) :
    IsNormalStarAlgEquiv e :=
  ⟨isProjectionSupremum_image_starAlgEquiv e,
    isProjectionSupremum_image_starAlgEquiv e.symm⟩

namespace TracialGroupFactorEquiv

def symm
    {G : CountableDiscreteGroup.{u}}
    {H : CountableDiscreteGroup.{v}}
    (e : TracialGroupFactorEquiv G H) :
    TracialGroupFactorEquiv H G where
  toStarAlgEquiv := e.toStarAlgEquiv.symm
  normal := ⟨e.normal.2, e.normal.1⟩
  trace_preserving := by
    intro y
    have h := e.trace_preserving (e.toStarAlgEquiv.symm y)
    simpa using h.symm

@[simp]
theorem symm_toStarAlgEquiv
    {G : CountableDiscreteGroup.{u}}
    {H : CountableDiscreteGroup.{v}}
    (e : TracialGroupFactorEquiv G H) :
    e.symm.toStarAlgEquiv = e.toStarAlgEquiv.symm :=
  rfl

end TracialGroupFactorEquiv

theorem tracialGroupFactorsIsomorphic_symm
    {G : CountableDiscreteGroup.{u}}
    {H : CountableDiscreteGroup.{v}} :
    TracialGroupFactorsIsomorphic G H →
      TracialGroupFactorsIsomorphic H G := by
  rintro ⟨e⟩
  exact ⟨e.symm⟩

end

end ConnesRigidity
