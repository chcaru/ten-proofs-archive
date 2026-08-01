


import ConnesRigidity.MultiplicationAlgebra










namespace ConnesRigidity

open MeasureTheory
open scoped ENNReal ComplexConjugate
noncomputable section

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def crossedCharacterDiagonalEquiv (v : IntegralLattice) :
    CrossedHilbert ≃ₗᵢ[ℂ] CrossedHilbert :=
  l2FiberwiseEquiv (fun _ => latticeCharacterMultiplierEquiv v)

def crossedOperatorBlock
    (T : CrossedHilbert →L[ℂ] CrossedHilbert)
    (q k : IntegralSymplecticGroup) :
    TorusL2 →L[ℂ] TorusL2 :=
  (lp.evalCLM ℂ (fun _ : IntegralSymplecticGroup => TorusL2) 2 q).comp <|
    T.comp <|
      lp.singleContinuousLinearMap ℂ
        (fun _ : IntegralSymplecticGroup => TorusL2) 2 k

@[simp]
theorem crossedOperatorBlock_apply
    (T : CrossedHilbert →L[ℂ] CrossedHilbert)
    (q k : IntegralSymplecticGroup) (f : TorusL2) :
    crossedOperatorBlock T q k f = T (lp.single 2 k f) q :=
  rfl

theorem crossedCharacterDiagonalEquiv_single
    (v : IntegralLattice) (k : IntegralSymplecticGroup)
    (f : TorusL2) :
    crossedCharacterDiagonalEquiv v (lp.single 2 k f) =
      lp.single 2 k (latticeCharacterMultiplierEquiv v f) :=
  l2FiberwiseEquiv_single _ _ _

theorem crossedOperatorBlock_commute_character
    (T : CrossedHilbert →L[ℂ] CrossedHilbert)
    (hT : ∀ v : IntegralLattice,
      Commute T
        (crossedCharacterDiagonalEquiv v :
          CrossedHilbert →L[ℂ] CrossedHilbert))
    (q k : IntegralSymplecticGroup) (v : IntegralLattice) :
    Commute (crossedOperatorBlock T q k)
      (latticeCharacterMultiplierEquiv v :
        TorusL2 →L[ℂ] TorusL2) := by
  change crossedOperatorBlock T q k *
      (latticeCharacterMultiplierEquiv v :
        TorusL2 →L[ℂ] TorusL2) =
    (latticeCharacterMultiplierEquiv v :
      TorusL2 →L[ℂ] TorusL2) * crossedOperatorBlock T q k
  apply ContinuousLinearMap.ext
  intro f
  change T (lp.single 2 k (latticeCharacterMultiplierEquiv v f)) q =
    latticeCharacterMultiplierEquiv v (T (lp.single 2 k f) q)
  rw [← crossedCharacterDiagonalEquiv_single]
  have hcomm := DFunLike.congr_fun (hT v).eq (lp.single 2 k f)
  change
    T (crossedCharacterDiagonalEquiv v (lp.single 2 k f)) q =
      crossedCharacterDiagonalEquiv v
        (T (lp.single 2 k f)) q
  exact congrFun (congrArg ((↑) : CrossedHilbert →
    (IntegralSymplecticGroup → TorusL2)) hcomm) q

private theorem measurable_torusCochain_conj'
    (g : IntegralSymplecticGroup) :
    Measurable (fun t => conj (torusCochain g t : ℂ)) :=
  Complex.continuous_conj.measurable.comp
    (measurable_torusCochain_complex g)

private theorem torusCochain_conj_norm'
    (g : IntegralSymplecticGroup) :
    ∀ t, ‖conj (torusCochain g t : ℂ)‖ = 1 := by
  intro t
  rw [Complex.norm_conj]
  exact Circle.norm_coe _

theorem crossedOperatorBlock_commute_cochain
    (T : CrossedHilbert →L[ℂ] CrossedHilbert)
    (hT : ∀ v : IntegralLattice,
      Commute T
        (crossedCharacterDiagonalEquiv v :
          CrossedHilbert →L[ℂ] CrossedHilbert))
    (q k g : IntegralSymplecticGroup) :
    Commute (crossedOperatorBlock T q k)
      (torusCochainInverseMultiplierEquiv g :
        TorusL2 →L[ℂ] TorusL2) := by
  simpa [torusCochainInverseMultiplierEquiv] using
    commute_unitMultiplier_of_commute_characters
      (crossedOperatorBlock T q k)
      (crossedOperatorBlock_commute_character T hT q k)
      (fun t => conj (torusCochain g t : ℂ))
      (measurable_torusCochain_conj' g)
      (torusCochain_conj_norm' g)

theorem commute_crossedCochainScalar_of_commute_characters
    (T : CrossedHilbert →L[ℂ] CrossedHilbert)
    (hT : ∀ v : IntegralLattice,
      Commute T
        (crossedCharacterDiagonalEquiv v :
          CrossedHilbert →L[ℂ] CrossedHilbert))
    (g : IntegralSymplecticGroup) :
    Commute T
      (crossedCochainScalarEquiv g :
        CrossedHilbert →L[ℂ] CrossedHilbert) := by
  change T * (crossedCochainScalarEquiv g :
      CrossedHilbert →L[ℂ] CrossedHilbert) =
    (crossedCochainScalarEquiv g :
      CrossedHilbert →L[ℂ] CrossedHilbert) * T
  apply ContinuousLinearMap.ext
  intro ξ
  classical
  have hmaps :
      (T * (crossedCochainScalarEquiv g :
        CrossedHilbert →L[ℂ] CrossedHilbert)) =
      ((crossedCochainScalarEquiv g :
        CrossedHilbert →L[ℂ] CrossedHilbert) * T) := by
    refine lp.ext_continuousLinearMap
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) fun k => ?_
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    funext q
    change
      (T * (crossedCochainScalarEquiv g :
        CrossedHilbert →L[ℂ] CrossedHilbert))
          (lp.single 2 k f) q =
        ((crossedCochainScalarEquiv g :
          CrossedHilbert →L[ℂ] CrossedHilbert) * T)
          (lp.single 2 k f) q
    rw [mul_apply_eq_comp, mul_apply_eq_comp]
    have hs :
        ((crossedCochainScalarEquiv g :
          CrossedHilbert ≃ₗᵢ[ℂ] CrossedHilbert) :
            CrossedHilbert →L[ℂ] CrossedHilbert)
            (lp.single 2 k f) =
          lp.single 2 k (torusCochainInverseMultiplierEquiv g f) :=
      crossedCochainScalarEquiv_single g k f
    rw [hs]
    change
      crossedOperatorBlock T q k
          (torusCochainInverseMultiplierEquiv g f) =
        torusCochainInverseMultiplierEquiv g
          (crossedOperatorBlock T q k f)
    exact DFunLike.congr_fun
      (crossedOperatorBlock_commute_cochain T hT q k g).eq f
  exact DFunLike.congr_fun hmaps ξ

end

end ConnesRigidity
