


import ConnesRigidity.CharacteristicSubgroup
import ConnesRigidity.ArithmeticCocycle
import ConnesRigidity.ICC
import ConnesRigidity.Statements
import ConnesRigidity.CrossedClosure
import ConnesRigidity.FiniteIndexEmbedding
import ConnesRigidity.PropertyTFiniteIndex
import ConnesRigidity.PropertyTExactCertificateOrbitProof














namespace ConnesRigidity


abbrev gammaZeroGroup : CountableDiscreteGroup :=
  constructedGammaZeroGroup


noncomputable abbrev gammaOneGroup : CountableDiscreteGroup :=
  constructedGammaOneGroup


theorem gammaZero_isICC : IsICC gammaZeroGroup := by
  constructor
  · exact cocycleExtension_infinite NormalizedAddCocycle.zero
  · intro x hx
    exact cocycleExtension_conjugacyClass_infinite x hx


theorem gammaOne_isICC : IsICC gammaOneGroup := by
  constructor
  · exact cocycleExtension_infinite integralSymplecticCocycleInput.twoCocycle
  · intro x hx
    exact cocycleExtension_conjugacyClass_infinite x hx



theorem gammaKernel_is_characteristic
    (f : IntegralSymplecticCocycleInput.GammaZero ≃*
      integralSymplecticCocycleInput.GammaOne) :
    CocycleExtension.PreservesKernel integralSymplecticCocycleInput.twoCocycle f :=
  gammaKernel_is_characteristic_proved f



theorem gammaZero_hasKazhdanPropertyT :
    HasKazhdanPropertyT gammaZeroGroup :=
  AffineSymplecticOrbitCertificate.constructedGammaZero_hasKazhdanPropertyT



theorem gammaGroupFactors_isomorphic :
    TracialGroupFactorsIsomorphic gammaZeroGroup gammaOneGroup :=
  constructedGroupFactors_isomorphic





theorem gammaOne_hasKazhdanPropertyT_of_gammaZero
    (hGT : HasKazhdanPropertyT gammaZeroGroup) :
    HasKazhdanPropertyT gammaOneGroup := by
  let S : Subgroup gammaZeroGroup := MonoidHom.range gammaOneToGammaZero
  letI : S.FiniteIndex := gammaOneToGammaZero_range_finiteIndex
  have hS : HasKazhdanPropertyT (gammaZeroGroup.subgroup S) :=
    hasKazhdanPropertyT_subgroup_of_finiteIndex gammaZeroGroup S hGT
  let e : gammaOneGroup ≃* gammaZeroGroup.subgroup S :=
    MonoidHom.ofInjective gammaOneToGammaZero_injective
  exact
    (hasKazhdanPropertyT_iff_of_mulEquiv
      gammaOneGroup (gammaZeroGroup.subgroup S) e).mpr hS

end ConnesRigidity
