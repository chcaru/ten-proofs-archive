


import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalLazyLex











namespace ConnesRigidity.AffineSymplecticOrbitCertificate


def canonicalPackedActionDigit (packed index : Nat) : Nat :=
  (packed >>> (6 * index)) % 64


def canonicalPackedActionSource (packed index : Nat) : Nat :=
  canonicalPackedActionDigit packed index % 32


def canonicalPackedActionSign (packed index : Nat) : Int :=
  if canonicalPackedActionDigit packed index < 32 then 1 else -1


def canonicalPackedActionArrayCoordinate
    (packed : Nat) (row : Array Int) (index : Nat) : Int :=
  canonicalPackedActionSign packed index *
    row.getD (canonicalPackedActionSource packed index) 0




def canonicalPackedActionCoordinate
    (packed sourcePacked index : Nat) : Int :=
  canonicalPackedActionSign packed index *
    (((sourcePacked >>>
      (4 * canonicalPackedActionSource packed index)) % 16 : Nat) - 8 : Int)




def canonicalPackedActionExpectedSource
    (symmetry : Array Int) (index : Nat) : Nat :=
  if index < 16 then
    4 * symmetryPermutationCoordinate symmetry (index / 4) +
      symmetryPermutationCoordinate symmetry (index % 4)
  else
    16 + symmetryPermutationCoordinate symmetry (index - 16)


def canonicalPackedActionExpectedSign
    (symmetry : Array Int) (index : Nat) : Int :=
  if index < 16 then
    symmetrySignCoordinate symmetry (index / 4) *
      symmetrySignCoordinate symmetry (index % 4)
  else
    symmetrySignCoordinate symmetry (index - 16)



theorem signedAffineCoordinate_eq_expected_packed_action
    (symmetry row : Array Int) (index : Nat) :
    signedAffineCoordinate symmetry row index =
      canonicalPackedActionExpectedSign symmetry index *
        row.getD (canonicalPackedActionExpectedSource symmetry index) 0 := by
  by_cases hindex : index < 16
  · simp [signedAffineCoordinate, canonicalPackedActionExpectedSign,
      canonicalPackedActionExpectedSource, hindex,
      signedActionMatrixCoordinate, matrixCoordinate]
  · simp [signedAffineCoordinate, canonicalPackedActionExpectedSign,
      canonicalPackedActionExpectedSource, hindex,
      signedActionVectorCoordinate, vectorCoordinate]



theorem canonicalPackedActionArrayCoordinate_eq_signedAffineCoordinate
    (packed : Nat) (symmetry row : Array Int) (index : Nat)
    (hsource : canonicalPackedActionSource packed index =
      canonicalPackedActionExpectedSource symmetry index)
    (hsign : canonicalPackedActionSign packed index =
      canonicalPackedActionExpectedSign symmetry index) :
    canonicalPackedActionArrayCoordinate packed row index =
      signedAffineCoordinate symmetry row index := by
  rw [signedAffineCoordinate_eq_expected_packed_action]
  simp [canonicalPackedActionArrayCoordinate, hsource, hsign]



theorem canonicalPackedActionCoordinate_eq_arrayCoordinate
    (packed sourcePacked index : Nat) (row : Array Int)
    (hsource :
      (((sourcePacked >>>
        (4 * canonicalPackedActionSource packed index)) % 16 : Nat) - 8 : Int) =
        row.getD (canonicalPackedActionSource packed index) 0) :
    canonicalPackedActionCoordinate packed sourcePacked index =
      canonicalPackedActionArrayCoordinate packed row index := by
  unfold canonicalPackedActionCoordinate
    canonicalPackedActionArrayCoordinate
  rw [hsource]

end ConnesRigidity.AffineSymplecticOrbitCertificate
