
import ConnesRigidity.ArithmeticCocycle
import ConnesRigidity.CharacteristicSubgroup
import ConnesRigidity.ICC
import ConnesRigidity.Statements
import ConnesRigidity.CrossedClosure

namespace ConnesRigidity

theorem groupsIsomorphic_symm
    {G H : CountableDiscreteGroup} :
    GroupsIsomorphic G H → GroupsIsomorphic H G := by
  rintro ⟨e⟩
  exact ⟨e.symm⟩

theorem not_connesRigidityAssertion_of_right_witness
    (G H : CountableDiscreteGroup.{0})
    (hHicc : IsICC H)
    (hHT : HasKazhdanPropertyT H)
    (hIso : TracialGroupFactorsIsomorphic G H)
    (hNotIso : ¬GroupsIsomorphic G H) :
    ¬ConnesRigidityAssertion := by
  intro hrigidity
  have hconclusion :=
    hrigidity H G hHicc hHT (tracialGroupFactorsIsomorphic_symm hIso)
  exact hNotIso (groupsIsomorphic_symm hconclusion.2)

theorem constructedGammaOne_isICC_feedback :
    IsICC constructedGammaOneGroup := by
  constructor
  · exact
      cocycleExtension_infinite
        integralSymplecticCocycleInput.twoCocycle
  · intro x hx
    exact cocycleExtension_conjugacyClass_infinite x hx

theorem constructedGammaZero_GammaOne_not_isomorphic_feedback :
    ¬GroupsIsomorphic constructedGammaZeroGroup constructedGammaOneGroup :=
  CocycleExtension.not_isomorphic_of_kernel_characteristic
    integralSymplecticCocycleInput.twoCocycle
    integralSymplecticCocycleInput.twoCocycle_not_isCoboundary
    gammaKernel_is_characteristic_proved

theorem connesRigidityAssertion_false_of_constructedGammaOne_propertyT
    (hT : HasKazhdanPropertyT constructedGammaOneGroup) :
    ¬ConnesRigidityAssertion :=
  not_connesRigidityAssertion_of_right_witness
    constructedGammaZeroGroup constructedGammaOneGroup
    constructedGammaOne_isICC_feedback hT
    constructedGroupFactors_isomorphic
    constructedGammaZero_GammaOne_not_isomorphic_feedback

end ConnesRigidity
