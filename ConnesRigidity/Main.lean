


import ConnesRigidity.ExternalResults








namespace ConnesRigidity


theorem quadratic_cocycle_defining_identity
    (g : IntegralSymplecticGroup) (w : ModTwoSpace) :
    standardQuadraticForm (g⁻¹ • w) + standardQuadraticForm w =
      modTwoSymplecticForm (integralSymplecticCocycleInput.d g) w :=
  integralSymplecticCocycleInput.defining_identity g w


theorem quadratic_cocycle_identity :
    groupCohomology.IsCocycle₁ integralSymplecticCocycleInput.d :=
  integralSymplecticCocycleInput.cocycle


noncomputable def integralTwoCocycle :
    NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice :=
  integralSymplecticCocycleInput.twoCocycle


theorem integralTwoCocycle_not_isCoboundary :
    ¬integralTwoCocycle.IsCoboundary :=
  integralSymplecticCocycleInput.twoCocycle_not_isCoboundary


theorem gammaOne_extension_does_not_split :
    IsEmpty
      (CocycleExtension.Splitting integralSymplecticCocycleInput.twoCocycle) :=
  integralSymplecticCocycleInput.gammaOne_has_no_splitting



theorem gammaZero_gammaOne_not_isomorphic :
    ¬GroupsIsomorphic gammaZeroGroup gammaOneGroup :=
  CocycleExtension.not_isomorphic_of_kernel_characteristic
    integralSymplecticCocycleInput.twoCocycle
    integralSymplecticCocycleInput.twoCocycle_not_isCoboundary
    gammaKernel_is_characteristic


theorem gammaOne_hasKazhdanPropertyT :
    HasKazhdanPropertyT gammaOneGroup :=
  gammaOne_hasKazhdanPropertyT_of_gammaZero
    gammaZero_hasKazhdanPropertyT


noncomputable def propertyTGroupFactorCounterexample :
    PropertyTGroupFactorCounterexample where
  Gamma := gammaZeroGroup
  Lambda := gammaOneGroup
  gamma_icc := gammaZero_isICC
  lambda_icc := gammaOne_isICC
  gamma_propertyT := gammaZero_hasKazhdanPropertyT
  lambda_propertyT := gammaOne_hasKazhdanPropertyT
  factors_isomorphic := gammaGroupFactors_isomorphic
  groups_not_isomorphic := gammaZero_gammaOne_not_isomorphic


theorem connesRigidityAssertion_false :
    ¬ConnesRigidityAssertion := by
  intro hrigidity
  have hconclusion :=
    hrigidity gammaZeroGroup gammaOneGroup gammaZero_isICC
      gammaZero_hasKazhdanPropertyT
      gammaGroupFactors_isomorphic
  exact gammaZero_gammaOne_not_isomorphic hconclusion.2

end ConnesRigidity
