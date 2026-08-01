
import ConnesRigidity.GammaZeroGenerators

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open Matrix

structure SignedNormalizer where
  matrix : Matrix SymplecticIndex SymplecticIndex ℤ
  sign : ℤ
  orthogonal : matrix * matrix.transpose = 1
  orthogonal' : matrix.transpose * matrix = 1
  sign_sq : sign * sign = 1
  form : matrix * Matrix.J (Fin 2) ℤ * matrix.transpose =
    sign • Matrix.J (Fin 2) ℤ
  form' : matrix.transpose * Matrix.J (Fin 2) ℤ * matrix =
    sign • Matrix.J (Fin 2) ℤ

namespace SignedNormalizer

variable (P : SignedNormalizer)

noncomputable local instance gammaZeroDecidableEq :
    DecidableEq IntegralSymplecticCocycleInput.GammaZero := Classical.decEq _

def identity : SignedNormalizer where
  matrix := 1
  sign := 1
  orthogonal := by simp
  orthogonal' := by simp
  sign_sq := by norm_num
  form := by simp
  form' := by simp

@[simp]
theorem identity_matrix :
    identity.matrix = (1 : Matrix SymplecticIndex SymplecticIndex ℤ) := rfl

@[simp]
theorem identity_sign : identity.sign = 1 := rfl

def symplecticConjugate (g : IntegralSymplecticGroup) :
    IntegralSymplecticGroup := by
  refine ⟨P.matrix * (g : Matrix SymplecticIndex SymplecticIndex ℤ) *
    P.matrix.transpose, ?_⟩
  rw [SymplecticGroup.mem_iff, Matrix.transpose_mul, Matrix.transpose_mul]
  calc
    (P.matrix * (g : Matrix SymplecticIndex SymplecticIndex ℤ) * P.matrix.transpose) *
        Matrix.J (Fin 2) ℤ *
          (P.matrix.transpose.transpose *
            ((g : Matrix SymplecticIndex SymplecticIndex ℤ).transpose *
              P.matrix.transpose)) =
      P.matrix * ((g : Matrix SymplecticIndex SymplecticIndex ℤ) *
        (P.matrix.transpose * Matrix.J (Fin 2) ℤ * P.matrix) *
          (g : Matrix SymplecticIndex SymplecticIndex ℤ).transpose) *
            P.matrix.transpose := by
              simp only [Matrix.transpose_transpose]
              noncomm_ring
    _ = P.sign • (P.matrix *
          ((g : Matrix SymplecticIndex SymplecticIndex ℤ) *
            Matrix.J (Fin 2) ℤ *
              (g : Matrix SymplecticIndex SymplecticIndex ℤ).transpose) *
                P.matrix.transpose) := by
          rw [P.form']
          simp only [mul_smul_comm, smul_mul_assoc]
    _ = P.sign • (P.matrix * Matrix.J (Fin 2) ℤ * P.matrix.transpose) := by
          rw [(SymplecticGroup.mem_iff.mp g.property)]
    _ = Matrix.J (Fin 2) ℤ := by
          rw [P.form, smul_smul, P.sign_sq, one_smul]

@[simp]
theorem symplecticConjugate_val (g : IntegralSymplecticGroup) :
    (P.symplecticConjugate g : Matrix SymplecticIndex SymplecticIndex ℤ) =
      P.matrix * (g : Matrix SymplecticIndex SymplecticIndex ℤ) *
        P.matrix.transpose := rfl

def transposeNormalizer : SignedNormalizer where
  matrix := P.matrix.transpose
  sign := P.sign
  orthogonal := by simpa only [Matrix.transpose_transpose] using P.orthogonal'
  orthogonal' := by simpa only [Matrix.transpose_transpose] using P.orthogonal
  sign_sq := P.sign_sq
  form := by simpa only [Matrix.transpose_transpose] using P.form'
  form' := by simpa only [Matrix.transpose_transpose] using P.form

@[simp]
theorem transposeNormalizer_matrix :
    P.transposeNormalizer.matrix = P.matrix.transpose := rfl

@[simp]
theorem transposeNormalizer_sign :
    P.transposeNormalizer.sign = P.sign := rfl

@[simp]
theorem transposeNormalizer_transposeNormalizer :
    P.transposeNormalizer.transposeNormalizer = P := by
  cases P
  rfl

@[simp]
theorem symplecticConjugate_mul
    (g h : IntegralSymplecticGroup) :
    P.symplecticConjugate (g * h) =
      P.symplecticConjugate g * P.symplecticConjugate h := by
  apply Subtype.ext
  change P.matrix *
      ((g : Matrix SymplecticIndex SymplecticIndex ℤ) *
        (h : Matrix SymplecticIndex SymplecticIndex ℤ)) *
        P.matrix.transpose =
      (P.matrix * (g : Matrix SymplecticIndex SymplecticIndex ℤ) *
        P.matrix.transpose) *
        (P.matrix * (h : Matrix SymplecticIndex SymplecticIndex ℤ) *
          P.matrix.transpose)
  calc
    _ = P.matrix * (g : Matrix SymplecticIndex SymplecticIndex ℤ) *
          (P.matrix.transpose * P.matrix) *
          (h : Matrix SymplecticIndex SymplecticIndex ℤ) *
          P.matrix.transpose := by
            rw [P.orthogonal']
            simp [mul_assoc]
    _ = _ := by noncomm_ring

@[simp]
theorem symplecticConjugate_one :
    P.symplecticConjugate 1 = 1 := by
  apply Subtype.ext
  simpa using P.orthogonal

@[simp]
theorem transposeNormalizer_symplecticConjugate
    (g : IntegralSymplecticGroup) :
    P.transposeNormalizer.symplecticConjugate
      (P.symplecticConjugate g) = g := by
  apply Subtype.ext
  change P.matrix.transpose *
      (P.matrix * (g : Matrix SymplecticIndex SymplecticIndex ℤ) *
        P.matrix.transpose) * P.matrix =
      (g : Matrix SymplecticIndex SymplecticIndex ℤ)
  calc
    _ = (P.matrix.transpose * P.matrix) *
          (g : Matrix SymplecticIndex SymplecticIndex ℤ) *
          (P.matrix.transpose * P.matrix) := by noncomm_ring
    _ = _ := by rw [P.orthogonal']; simp

theorem mulVec_smul
    (g : IntegralSymplecticGroup) (v : IntegralLattice) :
    P.matrix.mulVec (g • v) =
      P.symplecticConjugate g • P.matrix.mulVec v := by
  change P.matrix.mulVec
      ((g : Matrix SymplecticIndex SymplecticIndex ℤ).mulVec v) =
    (P.matrix * (g : Matrix SymplecticIndex SymplecticIndex ℤ) *
      P.matrix.transpose).mulVec (P.matrix.mulVec v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, P.orthogonal', Matrix.mul_one]

def gammaZeroMap (x : IntegralSymplecticCocycleInput.GammaZero) :
    IntegralSymplecticCocycleInput.GammaZero :=
  ⟨P.matrix.mulVec x.fst, P.symplecticConjugate x.snd⟩

@[simp]
theorem gammaZeroMap_fst (x : IntegralSymplecticCocycleInput.GammaZero) :
    (P.gammaZeroMap x).fst = P.matrix.mulVec x.fst := rfl

@[simp]
theorem gammaZeroMap_snd (x : IntegralSymplecticCocycleInput.GammaZero) :
    (P.gammaZeroMap x).snd = P.symplecticConjugate x.snd := rfl

theorem gammaZeroMap_mul (x y : IntegralSymplecticCocycleInput.GammaZero) :
    P.gammaZeroMap (x * y) = P.gammaZeroMap x * P.gammaZeroMap y := by
  apply CocycleExtension.ext
  · change P.matrix.mulVec (x.fst + x.snd • y.fst + 0) =
      P.matrix.mulVec x.fst +
        P.symplecticConjugate x.snd • P.matrix.mulVec y.fst + 0
    simp [Matrix.mulVec_add, P.mulVec_smul]
  · exact P.symplecticConjugate_mul x.snd y.snd

def gammaZeroEquiv :
    IntegralSymplecticCocycleInput.GammaZero ≃*
      IntegralSymplecticCocycleInput.GammaZero where
  toFun := P.gammaZeroMap
  invFun := P.transposeNormalizer.gammaZeroMap
  left_inv x := by
    apply CocycleExtension.ext
    · change P.matrix.transpose.mulVec (P.matrix.mulVec x.fst) = x.fst
      rw [Matrix.mulVec_mulVec, P.orthogonal', Matrix.one_mulVec]
    · exact P.transposeNormalizer_symplecticConjugate x.snd
  right_inv x := by
    apply CocycleExtension.ext
    · change P.matrix.mulVec (P.matrix.transpose.mulVec x.fst) = x.fst
      rw [Matrix.mulVec_mulVec, P.orthogonal, Matrix.one_mulVec]
    · simpa using
        P.transposeNormalizer.transposeNormalizer_symplecticConjugate x.snd
  map_mul' := P.gammaZeroMap_mul

@[simp]
theorem gammaZeroEquiv_fst (x : IntegralSymplecticCocycleInput.GammaZero) :
    (P.gammaZeroEquiv x).fst = P.matrix.mulVec x.fst := rfl

@[simp]
theorem gammaZeroEquiv_snd (x : IntegralSymplecticCocycleInput.GammaZero) :
    (P.gammaZeroEquiv x).snd = P.symplecticConjugate x.snd := rfl

theorem gammaZeroEquiv_ext_of_matrix_eq
    {Q : SignedNormalizer} (h : P.matrix = Q.matrix) :
    P.gammaZeroEquiv = Q.gammaZeroEquiv := by
  apply MulEquiv.ext
  intro x
  apply CocycleExtension.ext
  · simp [h]
  · apply Subtype.ext
    simp [symplecticConjugate_val, h]

theorem gammaZeroEquiv_trans_of_matrix_mul
    (Q R : SignedNormalizer) (h : R.matrix = P.matrix * Q.matrix) :
    Q.gammaZeroEquiv.trans P.gammaZeroEquiv = R.gammaZeroEquiv := by
  apply MulEquiv.ext
  intro x
  apply CocycleExtension.ext
  · change P.matrix.mulVec (Q.matrix.mulVec x.fst) = R.matrix.mulVec x.fst
    rw [Matrix.mulVec_mulVec, h]
  · apply Subtype.ext
    change P.matrix *
        (Q.matrix * (x.snd : Matrix SymplecticIndex SymplecticIndex ℤ) *
          Q.matrix.transpose) * P.matrix.transpose =
        R.matrix * (x.snd : Matrix SymplecticIndex SymplecticIndex ℤ) *
          R.matrix.transpose
    rw [h, Matrix.transpose_mul]
    noncomm_ring

@[simp]
theorem gammaZeroEquiv_symm_apply
    (x : IntegralSymplecticCocycleInput.GammaZero) :
    P.gammaZeroEquiv.symm x = P.transposeNormalizer.gammaZeroEquiv x := rfl

@[simp]
theorem gammaZeroEquiv_translation (v : IntegralLattice) :
    P.gammaZeroEquiv
        ({ fst := v, snd := (1 : IntegralSymplecticGroup) } :
          IntegralSymplecticCocycleInput.GammaZero) =
      ({ fst := P.matrix.mulVec v,
          snd := (1 : IntegralSymplecticGroup) } :
        IntegralSymplecticCocycleInput.GammaZero) := by
  apply CocycleExtension.ext
  · rfl
  · exact P.symplecticConjugate_one

@[simp]
theorem gammaZeroEquiv_basisTranslation (i : SymplecticIndex) :
    P.gammaZeroEquiv (gammaZeroBasisTranslation i) =
      ({ fst := P.matrix.mulVec (Pi.single i 1),
          snd := (1 : IntegralSymplecticGroup) } :
        IntegralSymplecticCocycleInput.GammaZero) := by
  exact P.gammaZeroEquiv_translation (Pi.single i 1)

@[simp]
theorem gammaZeroEquiv_quotientLift (g : IntegralSymplecticGroup) :
    P.gammaZeroEquiv (gammaZeroQuotientLift g) =
      gammaZeroQuotientLift (P.symplecticConjugate g) := by
  apply CocycleExtension.ext
  · exact Matrix.mulVec_zero P.matrix
  · rfl

theorem gammaZeroEquiv_image_generators_of_mem
    (hpreserve : ∀ g ∈ gammaZeroElementaryGenerators,
      P.gammaZeroEquiv g ∈ gammaZeroElementaryGenerators) :
    gammaZeroElementaryGenerators.image P.gammaZeroEquiv =
      gammaZeroElementaryGenerators := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro g hg
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hg
    exact hpreserve h hh
  · rw [Finset.card_image_of_injective _ P.gammaZeroEquiv.injective]

end SignedNormalizer

end ConnesRigidity.AffineSymplecticOrbitCertificate
