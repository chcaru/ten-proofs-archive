


import ConnesRigidity.PropertyTExactCertificateOrbitBasisTransport


























namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open Matrix
open scoped BigOperators

noncomputable section



def coefficientProfileVertex (element : constructedGammaZeroGroup)
    (sign : Int) (index : Fin 4) : List Int :=
  let matrix : Matrix SymplecticIndex SymplecticIndex Int := element.snd
  let vector := element.fst
  let coordinate := coordinateIndex index
  let gram := matrix.transpose * matrix
  let twisted := Matrix.J (Fin 2) Int * matrix
  [|(matrix.transpose.mulVec vector) coordinate|,
   matrix coordinate coordinate,
   ∑ other : SymplecticIndex, gram coordinate other ^ 2,
   |(twisted.mulVec vector) coordinate|,
   sign * twisted coordinate coordinate,
   ∑ other : SymplecticIndex, twisted coordinate other ^ 2]


def coefficientProfileOrientation
    (element : constructedGammaZeroGroup) (sign : Int) : List (List Int) :=
  (List.ofFn fun index : Fin 4 =>
    coefficientProfileVertex element sign index).mergeSort (· ≤ ·)


def coefficientProfileUnsigned
    (element : constructedGammaZeroGroup) : List (List Int) :=
  min (coefficientProfileOrientation element 1)
    (coefficientProfileOrientation element (-1))






def coefficientProfile
    (element : constructedGammaZeroGroup) :
      List (List Int) × List (List Int) :=
  (min (coefficientProfileUnsigned element)
      (coefficientProfileUnsigned element⁻¹),
   max (coefficientProfileUnsigned element)
      (coefficientProfileUnsigned element⁻¹))



@[simp] theorem coefficientProfile_inv
    (element : constructedGammaZeroGroup) :
    coefficientProfile element⁻¹ = coefficientProfile element := by
  simp [coefficientProfile, min_comm, max_comm]

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
