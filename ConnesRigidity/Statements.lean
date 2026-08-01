
import ConnesRigidity.GroupVonNeumannAlgebra
import ConnesRigidity.PropertyT

namespace ConnesRigidity

universe u

structure PropertyTGroupFactorCounterexample where
  Gamma : CountableDiscreteGroup.{u}
  Lambda : CountableDiscreteGroup.{u}
  gamma_icc : IsICC Gamma
  lambda_icc : IsICC Lambda
  gamma_propertyT : HasKazhdanPropertyT Gamma
  lambda_propertyT : HasKazhdanPropertyT Lambda
  factors_isomorphic : TracialGroupFactorsIsomorphic Gamma Lambda
  groups_not_isomorphic : ¬GroupsIsomorphic Gamma Lambda

end ConnesRigidity
