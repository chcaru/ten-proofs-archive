


import ConnesRigidity.PropertyTExactCertificateOrbitData
import ConnesRigidity.PropertyTExactCertificateOrbitSymmetry











namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open Matrix


def certificateIndex (i : SymplecticIndex) : Fin 4 :=
  (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin (2 + 2)) i


def matrixCoordinate (row : Array Int) (i j : Nat) : Int :=
  row.getD (4 * i + j) 0


def vectorCoordinate (row : Array Int) (i : Nat) : Int :=
  row.getD (16 + i) 0


def matrixOfRow (row : Array Int) :
    Matrix SymplecticIndex SymplecticIndex Int :=
  fun i j => matrixCoordinate row (certificateIndex i).val
    (certificateIndex j).val


def vectorOfRow (row : Array Int) : IntegralLattice :=
  fun i => vectorCoordinate row (certificateIndex i).val

@[simp] theorem matrixOfRow_apply (row : Array Int)
    (i j : SymplecticIndex) :
    matrixOfRow row i j =
      row.getD (4 * (certificateIndex i).val +
        (certificateIndex j).val) 0 := rfl

@[simp] theorem vectorOfRow_apply (row : Array Int)
    (i : SymplecticIndex) :
    vectorOfRow row i = row.getD (16 + (certificateIndex i).val) 0 := rfl


def matrixRowPairing (row : Array Int) (i j : Nat) : Int :=
  matrixCoordinate row i 0 * matrixCoordinate row j 2 +
    matrixCoordinate row i 1 * matrixCoordinate row j 3 -
      matrixCoordinate row i 2 * matrixCoordinate row j 0 -
        matrixCoordinate row i 3 * matrixCoordinate row j 1



def isSymplecticRow (row : Array Int) : Bool :=
  let matrix := matrixOfRow row
  decide (∀ i j : SymplecticIndex,
    (matrix * Matrix.J (Fin 2) Int * matrix.transpose) i j =
      Matrix.J (Fin 2) Int i j)


theorem matrixOfRow_mem_symplectic {row : Array Int}
    (h : isSymplecticRow row = true) :
    matrixOfRow row ∈ Matrix.symplecticGroup (Fin 2) Int := by
  rw [SymplecticGroup.mem_iff]
  ext i j
  exact (of_decide_eq_true h) i j




def gammaZeroOfRow (row : Array Int) : constructedGammaZeroGroup :=
  if h : isSymplecticRow row = true then
    { fst := vectorOfRow row
      snd := ⟨matrixOfRow row, matrixOfRow_mem_symplectic h⟩ }
  else
    1

@[simp] theorem gammaZeroOfRow_fst_of_symplectic
    {row : Array Int} (h : isSymplecticRow row = true) :
    (gammaZeroOfRow row).fst = vectorOfRow row := by
  simp [gammaZeroOfRow, h]

@[simp] theorem gammaZeroOfRow_snd_of_symplectic
    {row : Array Int} (h : isSymplecticRow row = true) :
    ((gammaZeroOfRow row).snd :
      Matrix SymplecticIndex SymplecticIndex Int) = matrixOfRow row := by
  simp [gammaZeroOfRow, h]


noncomputable def basisElement (i : Nat) : constructedGammaZeroGroup :=
  gammaZeroOfRow (basisData.getD i #[])



noncomputable def orbitBasis (i : Fin 425) : constructedGammaZeroGroup :=
  basisElement i.val


noncomputable def coefficientRepresentativeElement
    (orbit : Nat) : constructedGammaZeroGroup :=
  gammaZeroOfRow (coefficientRepresentativeData.getD orbit #[])


noncomputable abbrev certificateBasis (i : Fin 425) :
    constructedGammaZeroGroup := orbitBasis i


noncomputable def generatorElements : List constructedGammaZeroGroup :=
  generatorData.toList.map gammaZeroOfRow


noncomputable def generatorElement (i : Nat) : constructedGammaZeroGroup :=
  gammaZeroOfRow (generatorData.getD i #[])



noncomputable def basisRowsSymplecticCheck : Bool :=
  basisData.all isSymplecticRow



noncomputable def generatorRowsSymplecticCheck : Bool :=
  generatorData.all isSymplecticRow


def symmetryPermutationCoordinate (row : Array Int) (i : Nat) : Nat :=
  (row.getD i 0).toNat


def symmetrySignCoordinate (row : Array Int) (i : Nat) : Int :=
  row.getD (4 + i) 0



def signedMatrixOfRow (row : Array Int) :
    Matrix SymplecticIndex SymplecticIndex Int :=
  fun i j =>
    if (certificateIndex j).val =
        symmetryPermutationCoordinate row (certificateIndex i).val then
      symmetrySignCoordinate row (certificateIndex i).val
    else
      0



def isSignedNormalizerRow (row : Array Int) : Bool :=
  let matrix := signedMatrixOfRow row
  let sign := row.getD 8 0
  decide (∀ i j : SymplecticIndex,
    (matrix * matrix.transpose) i j = (1 : Matrix _ _ Int) i j) &&
    (decide (∀ i j : SymplecticIndex,
      (matrix.transpose * matrix) i j = (1 : Matrix _ _ Int) i j) &&
      (decide (sign * sign = 1) &&
        (decide (∀ i j : SymplecticIndex,
          (matrix * Matrix.J (Fin 2) Int * matrix.transpose) i j =
            (sign • Matrix.J (Fin 2) Int) i j) &&
          decide (∀ i j : SymplecticIndex,
            (matrix.transpose * Matrix.J (Fin 2) Int * matrix) i j =
              (sign • Matrix.J (Fin 2) Int) i j))))



def signedNormalizerOfRow (row : Array Int) : SignedNormalizer :=
  if h : isSignedNormalizerRow row = true then
    { matrix := signedMatrixOfRow row
      sign := row.getD 8 0
      orthogonal := by
        simp only [isSignedNormalizerRow, Bool.and_eq_true,
          decide_eq_true_eq] at h
        exact Matrix.ext h.1
      orthogonal' := by
        simp only [isSignedNormalizerRow, Bool.and_eq_true,
          decide_eq_true_eq] at h
        exact Matrix.ext h.2.1
      sign_sq := by
        simp only [isSignedNormalizerRow, Bool.and_eq_true,
          decide_eq_true_eq] at h
        exact h.2.2.1
      form := by
        simp only [isSignedNormalizerRow, Bool.and_eq_true,
          decide_eq_true_eq] at h
        exact Matrix.ext h.2.2.2.1
      form' := by
        simp only [isSignedNormalizerRow, Bool.and_eq_true,
          decide_eq_true_eq] at h
        exact Matrix.ext h.2.2.2.2 }
  else
    SignedNormalizer.identity

@[simp] theorem signedNormalizerOfRow_matrix_of_check
    {row : Array Int} (h : isSignedNormalizerRow row = true) :
    (signedNormalizerOfRow row).matrix = signedMatrixOfRow row := by
  simp [signedNormalizerOfRow, h]

@[simp] theorem signedNormalizerOfRow_sign_of_check
    {row : Array Int} (h : isSignedNormalizerRow row = true) :
    (signedNormalizerOfRow row).sign = row.getD 8 0 := by
  simp [signedNormalizerOfRow, h]


noncomputable def symmetryNormalizer (s : Nat) : SignedNormalizer :=
  signedNormalizerOfRow (symmetryData.getD s #[])


noncomputable def orbitSymmetry (s : Fin 64) :
    constructedGammaZeroGroup ≃* constructedGammaZeroGroup :=
  (symmetryNormalizer s.val).gammaZeroEquiv

end ConnesRigidity.AffineSymplecticOrbitCertificate
