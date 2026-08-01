


import ConnesRigidity.PropertyTExactCertificateOrbitBasisTransport










namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open Matrix
open scoped BigOperators


def profileSourceIndex
    (symmetry : Array Int) (h : isSignedNormalizerRow symmetry = true)
    (i : SymplecticIndex) : SymplecticIndex :=
  coordinateIndex
    ⟨symmetryPermutationCoordinate symmetry (certificateIndex i).val,
      symmetryPermutationCoordinate_lt h (certificateIndex i)⟩



theorem profileSymmetrySign_sq
    {symmetry : Array Int} (h : isSignedNormalizerRow symmetry = true)
    (i : SymplecticIndex) :
    symmetrySignCoordinate symmetry (certificateIndex i).val *
      symmetrySignCoordinate symmetry (certificateIndex i).val = 1 := by
  have hsource := symmetryPermutationCoordinate_lt h (certificateIndex i)
  have hentry := signedMatrixOfRow_conjugate_apply_of_coordinate_lt
    symmetry (1 : Matrix SymplecticIndex SymplecticIndex Int)
    i i hsource hsource
  have horthogonal := (signedNormalizerOfRow symmetry).orthogonal
  rw [signedNormalizerOfRow_matrix_of_check h] at horthogonal
  simpa [horthogonal] using hentry.symm


theorem profileSymmetrySign_abs
    {symmetry : Array Int} (h : isSignedNormalizerRow symmetry = true)
    (i : SymplecticIndex) :
    |symmetrySignCoordinate symmetry (certificateIndex i).val| = 1 := by
  rcases mul_self_eq_one_iff.mp (profileSymmetrySign_sq h i) with hsign | hsign
  · simp [hsign]
  · simp [hsign]



theorem profileSymmetryMultiplier_abs
    {symmetry : Array Int} (h : isSignedNormalizerRow symmetry = true) :
    |symmetry.getD 8 0| = 1 := by
  have hsign := (signedNormalizerOfRow symmetry).sign_sq
  rw [signedNormalizerOfRow_sign_of_check h] at hsign
  rcases mul_self_eq_one_iff.mp hsign with hpositive | hnegative
  · simp [hpositive]
  · simp [hnegative]



theorem profileSourceIndex_injective
    {symmetry : Array Int} (h : isSignedNormalizerRow symmetry = true) :
    Function.Injective (profileSourceIndex symmetry h) := by
  intro i j heq
  by_contra hne
  have hi := symmetryPermutationCoordinate_lt h (certificateIndex i)
  have hj := symmetryPermutationCoordinate_lt h (certificateIndex j)
  have hentry := signedMatrixOfRow_conjugate_apply_of_coordinate_lt
    symmetry (1 : Matrix SymplecticIndex SymplecticIndex Int) i j hi hj
  have horthogonal := (signedNormalizerOfRow symmetry).orthogonal
  rw [signedNormalizerOfRow_matrix_of_check h] at horthogonal
  have hselected :
      coordinateIndex
        ⟨symmetryPermutationCoordinate symmetry (certificateIndex i).val, hi⟩ =
      coordinateIndex
        ⟨symmetryPermutationCoordinate symmetry (certificateIndex j).val, hj⟩ :=
    heq
  have hzero :
      symmetrySignCoordinate symmetry (certificateIndex i).val *
        symmetrySignCoordinate symmetry (certificateIndex j).val = 0 := by
    rw [hselected] at hentry
    simpa only [Matrix.mul_one, horthogonal, Matrix.one_apply,
      if_neg hne, if_pos rfl, ite_true, mul_one] using hentry.symm
  have hleft : symmetrySignCoordinate symmetry (certificateIndex i).val ≠ 0 := by
    intro hzero'
    simpa [hzero'] using profileSymmetrySign_sq h i
  have hright : symmetrySignCoordinate symmetry (certificateIndex j).val ≠ 0 := by
    intro hzero'
    simpa [hzero'] using profileSymmetrySign_sq h j
  exact (mul_ne_zero hleft hright) hzero



noncomputable def profilePermutation
    (symmetry : Array Int) (h : isSignedNormalizerRow symmetry = true) :
    SymplecticIndex ≃ SymplecticIndex :=
  Equiv.ofBijective (profileSourceIndex symmetry h)
    ⟨profileSourceIndex_injective h,
      Finite.injective_iff_surjective.mp
        (profileSourceIndex_injective h)⟩

@[simp] theorem profilePermutation_apply
    (symmetry : Array Int) (h : isSignedNormalizerRow symmetry = true)
    (i : SymplecticIndex) :
    profilePermutation symmetry h i = profileSourceIndex symmetry h i := rfl


theorem profileConjugate_apply
    {symmetry : Array Int} (h : isSignedNormalizerRow symmetry = true)
    (matrix : Matrix SymplecticIndex SymplecticIndex Int)
    (i j : SymplecticIndex) :
    (signedMatrixOfRow symmetry * matrix *
        (signedMatrixOfRow symmetry).transpose) i j =
      symmetrySignCoordinate symmetry (certificateIndex i).val *
        symmetrySignCoordinate symmetry (certificateIndex j).val *
        matrix (profilePermutation symmetry h i)
          (profilePermutation symmetry h j) := by
  exact signedMatrixOfRow_conjugate_apply_of_coordinate_lt symmetry matrix i j
    (symmetryPermutationCoordinate_lt h (certificateIndex i))
    (symmetryPermutationCoordinate_lt h (certificateIndex j))


theorem profileConjugate_diagonal
    {symmetry : Array Int} (h : isSignedNormalizerRow symmetry = true)
    (matrix : Matrix SymplecticIndex SymplecticIndex Int)
    (i : SymplecticIndex) :
    (signedMatrixOfRow symmetry * matrix *
        (signedMatrixOfRow symmetry).transpose) i i =
      matrix (profilePermutation symmetry h i)
        (profilePermutation symmetry h i) := by
  rw [profileConjugate_apply h]
  rw [profileSymmetrySign_sq h i]
  simp


theorem profileConjugate_abs_apply
    {symmetry : Array Int} (h : isSignedNormalizerRow symmetry = true)
    (matrix : Matrix SymplecticIndex SymplecticIndex Int)
    (i j : SymplecticIndex) :
    |(signedMatrixOfRow symmetry * matrix *
        (signedMatrixOfRow symmetry).transpose) i j| =
      |matrix (profilePermutation symmetry h i)
        (profilePermutation symmetry h j)| := by
  rw [profileConjugate_apply h, abs_mul, abs_mul,
    profileSymmetrySign_abs h i, profileSymmetrySign_abs h j]
  simp


theorem profileConjugate_transpose
    (symmetry : Array Int)
    (matrix : Matrix SymplecticIndex SymplecticIndex Int) :
    (signedMatrixOfRow symmetry * matrix *
        (signedMatrixOfRow symmetry).transpose).transpose =
      signedMatrixOfRow symmetry * matrix.transpose *
        (signedMatrixOfRow symmetry).transpose := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  noncomm_ring


theorem profileConjugate_gram
    {symmetry : Array Int} (h : isSignedNormalizerRow symmetry = true)
    (matrix : Matrix SymplecticIndex SymplecticIndex Int) :
    (signedMatrixOfRow symmetry * matrix *
        (signedMatrixOfRow symmetry).transpose).transpose *
      (signedMatrixOfRow symmetry * matrix *
        (signedMatrixOfRow symmetry).transpose) =
      signedMatrixOfRow symmetry * (matrix.transpose * matrix) *
        (signedMatrixOfRow symmetry).transpose := by
  rw [profileConjugate_transpose]
  have horthogonal := (signedNormalizerOfRow symmetry).orthogonal'
  rw [signedNormalizerOfRow_matrix_of_check h] at horthogonal
  calc
    (signedMatrixOfRow symmetry * matrix.transpose *
        (signedMatrixOfRow symmetry).transpose) *
      (signedMatrixOfRow symmetry * matrix *
        (signedMatrixOfRow symmetry).transpose) =
      signedMatrixOfRow symmetry * matrix.transpose *
        ((signedMatrixOfRow symmetry).transpose *
          signedMatrixOfRow symmetry) * matrix *
            (signedMatrixOfRow symmetry).transpose := by noncomm_ring
    _ = _ := by rw [horthogonal]; simp [Matrix.mul_assoc]



theorem profileConjugate_symplectic
    {symmetry : Array Int} (h : isSignedNormalizerRow symmetry = true)
    (matrix : Matrix SymplecticIndex SymplecticIndex Int) :
    Matrix.J (Fin 2) Int *
      (signedMatrixOfRow symmetry * matrix *
        (signedMatrixOfRow symmetry).transpose) =
      symmetry.getD 8 0 •
        (signedMatrixOfRow symmetry * (Matrix.J (Fin 2) Int * matrix) *
          (signedMatrixOfRow symmetry).transpose) := by
  let normalizer := signedNormalizerOfRow symmetry
  have hmatrix : normalizer.matrix = signedMatrixOfRow symmetry :=
    signedNormalizerOfRow_matrix_of_check h
  have hsign : normalizer.sign = symmetry.getD 8 0 :=
    signedNormalizerOfRow_sign_of_check h
  have hcommute :
      Matrix.J (Fin 2) Int * normalizer.matrix =
        normalizer.sign • (normalizer.matrix * Matrix.J (Fin 2) Int) := by
    calc
      Matrix.J (Fin 2) Int * normalizer.matrix =
          normalizer.matrix *
            (normalizer.matrix.transpose * Matrix.J (Fin 2) Int *
              normalizer.matrix) := by
                symm
                calc
                  normalizer.matrix *
                      (normalizer.matrix.transpose * Matrix.J (Fin 2) Int *
                        normalizer.matrix) =
                    (normalizer.matrix * normalizer.matrix.transpose) *
                      (Matrix.J (Fin 2) Int * normalizer.matrix) := by
                        noncomm_ring
                  _ = _ := by rw [normalizer.orthogonal]; simp
      _ = normalizer.matrix *
          (normalizer.sign • Matrix.J (Fin 2) Int) := by
            rw [normalizer.form']
      _ = normalizer.sign •
          (normalizer.matrix * Matrix.J (Fin 2) Int) := by
            exact Matrix.mul_smul normalizer.matrix normalizer.sign
              (Matrix.J (Fin 2) Int)
  rw [← hmatrix, ← hsign]
  calc
    Matrix.J (Fin 2) Int *
        (normalizer.matrix * matrix * normalizer.matrix.transpose) =
      (Matrix.J (Fin 2) Int * normalizer.matrix) *
        matrix * normalizer.matrix.transpose := by noncomm_ring
    _ = (normalizer.sign •
        (normalizer.matrix * Matrix.J (Fin 2) Int)) *
          matrix * normalizer.matrix.transpose := by rw [hcommute]
    _ = normalizer.sign •
        (normalizer.matrix * (Matrix.J (Fin 2) Int * matrix) *
          normalizer.matrix.transpose) := by
            simp [Matrix.mul_assoc]


theorem profileConjugate_mulVec
    {symmetry : Array Int} (h : isSignedNormalizerRow symmetry = true)
    (matrix : Matrix SymplecticIndex SymplecticIndex Int)
    (vector : IntegralLattice) :
    (signedMatrixOfRow symmetry * matrix *
        (signedMatrixOfRow symmetry).transpose).mulVec
      ((signedMatrixOfRow symmetry).mulVec vector) =
        (signedMatrixOfRow symmetry).mulVec (matrix.mulVec vector) := by
  have horthogonal := (signedNormalizerOfRow symmetry).orthogonal'
  rw [signedNormalizerOfRow_matrix_of_check h] at horthogonal
  calc
    (signedMatrixOfRow symmetry * matrix *
          (signedMatrixOfRow symmetry).transpose).mulVec
        ((signedMatrixOfRow symmetry).mulVec vector) =
      ((signedMatrixOfRow symmetry * matrix *
          (signedMatrixOfRow symmetry).transpose) *
        signedMatrixOfRow symmetry).mulVec vector := by
          rw [Matrix.mulVec_mulVec]
    _ = (signedMatrixOfRow symmetry * matrix).mulVec vector := by
      congr 1
      calc
        (signedMatrixOfRow symmetry * matrix *
            (signedMatrixOfRow symmetry).transpose) *
          signedMatrixOfRow symmetry =
            signedMatrixOfRow symmetry * matrix *
              ((signedMatrixOfRow symmetry).transpose *
                signedMatrixOfRow symmetry) := by noncomm_ring
        _ = _ := by rw [horthogonal]; simp
    _ = (signedMatrixOfRow symmetry).mulVec (matrix.mulVec vector) := by
      rw [Matrix.mulVec_mulVec]



theorem profileConjugate_mulVec_abs
    {symmetry : Array Int} (h : isSignedNormalizerRow symmetry = true)
    (matrix : Matrix SymplecticIndex SymplecticIndex Int)
    (vector : IntegralLattice) (i : SymplecticIndex) :
    |(signedMatrixOfRow symmetry * matrix *
        (signedMatrixOfRow symmetry).transpose).mulVec
          ((signedMatrixOfRow symmetry).mulVec vector) i| =
      |matrix.mulVec vector (profilePermutation symmetry h i)| := by
  rw [profileConjugate_mulVec h]
  rw [signedMatrixOfRow_mulVec_apply_of_coordinate_lt symmetry
    (matrix.mulVec vector) i
    (symmetryPermutationCoordinate_lt h (certificateIndex i))]
  rw [abs_mul, profileSymmetrySign_abs h i]
  simp [profilePermutation, profileSourceIndex]



theorem profileScaledConjugate_mulVec_abs
    {symmetry : Array Int} (h : isSignedNormalizerRow symmetry = true)
    (matrix : Matrix SymplecticIndex SymplecticIndex Int)
    (vector : IntegralLattice) (i : SymplecticIndex) :
    |(symmetry.getD 8 0 •
        (signedMatrixOfRow symmetry * matrix *
          (signedMatrixOfRow symmetry).transpose)).mulVec
            ((signedMatrixOfRow symmetry).mulVec vector) i| =
      |matrix.mulVec vector (profilePermutation symmetry h i)| := by
  rw [Matrix.smul_mulVec]
  change |symmetry.getD 8 0 *
      (signedMatrixOfRow symmetry * matrix *
        (signedMatrixOfRow symmetry).transpose).mulVec
          ((signedMatrixOfRow symmetry).mulVec vector) i| = _
  rw [abs_mul, profileSymmetryMultiplier_abs h,
    profileConjugate_mulVec_abs h]
  simp


theorem profileConjugate_row_sq_sum
    {symmetry : Array Int} (h : isSignedNormalizerRow symmetry = true)
    (matrix : Matrix SymplecticIndex SymplecticIndex Int)
    (i : SymplecticIndex) :
    (∑ j : SymplecticIndex,
      ((signedMatrixOfRow symmetry * matrix *
        (signedMatrixOfRow symmetry).transpose) i j) ^ 2) =
      ∑ j : SymplecticIndex,
        (matrix (profilePermutation symmetry h i) j) ^ 2 := by
  calc
    (∑ j : SymplecticIndex,
      ((signedMatrixOfRow symmetry * matrix *
        (signedMatrixOfRow symmetry).transpose) i j) ^ 2) =
        ∑ j : SymplecticIndex,
          (matrix (profilePermutation symmetry h i)
            (profilePermutation symmetry h j)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [profileConjugate_apply h, mul_pow, mul_pow]
            simp only [pow_two, profileSymmetrySign_sq h i,
              profileSymmetrySign_sq h j, one_mul]
    _ = _ := Equiv.sum_comp (profilePermutation symmetry h)
      (fun j => (matrix (profilePermutation symmetry h i) j) ^ 2)

end ConnesRigidity.AffineSymplecticOrbitCertificate
