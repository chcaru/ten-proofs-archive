


import ConnesRigidity.ICC
import ConnesRigidity.CharacteristicKernel
import Mathlib.Tactic.NoncommRing











namespace ConnesRigidity

open Matrix

def characteristicSymplecticForm
    (x y : IntegralLattice) : ℤ :=
  ∑ i : Fin 2,
    (-x (Sum.inl i) * y (Sum.inr i) +
      x (Sum.inr i) * y (Sum.inl i))

def symplecticCovector
    (v : IntegralLattice) : IntegralLattice
  | Sum.inl i => -v (Sum.inr i)
  | Sum.inr i => v (Sum.inl i)

def symplecticRankOne
    (v : IntegralLattice) :
    Matrix SymplecticIndex SymplecticIndex ℤ :=
  fun i j => v i * symplecticCovector v j

def symplecticTransvectionMatrix
    (v : IntegralLattice) (n : ℤ) :
    Matrix SymplecticIndex SymplecticIndex ℤ :=
  fun i j => (1 : Matrix SymplecticIndex SymplecticIndex ℤ) i j +
    n * symplecticRankOne v i j

theorem symplecticTransvectionMatrix_mem
    (v : IntegralLattice) (n : ℤ) :
    symplecticTransvectionMatrix v n ∈
      Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticTransvectionMatrix, symplecticRankOne,
      symplecticCovector, Matrix.J, Matrix.fromBlocks,
      Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two] <;>
    ring

def symplecticTransvection
    (v : IntegralLattice) (n : ℤ) :
    IntegralSymplecticGroup :=
  ⟨symplecticTransvectionMatrix v n,
    symplecticTransvectionMatrix_mem v n⟩

theorem characteristicSymplecticForm_eq_dotProduct
    (x y : IntegralLattice) :
    characteristicSymplecticForm x y =
      dotProduct x
        ((Matrix.J (Fin 2) ℤ).mulVec y) := by
  simp [characteristicSymplecticForm, Matrix.J, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  ring

theorem characteristicSymplecticForm_smul
    (g : IntegralSymplecticGroup)
    (x y : IntegralLattice) :
    characteristicSymplecticForm (g • x) (g • y) =
      characteristicSymplecticForm x y := by
  rw [characteristicSymplecticForm_eq_dotProduct,
    characteristicSymplecticForm_eq_dotProduct]
  change dotProduct (g.1.mulVec x)
      ((Matrix.J (Fin 2) ℤ).mulVec (g.1.mulVec y)) =
    dotProduct x ((Matrix.J (Fin 2) ℤ).mulVec y)
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [SymplecticGroup.mem_iff'.mp g.2]
  rw [← Matrix.dotProduct_mulVec]

theorem symplecticRankOne_mulVec
    (v x : IntegralLattice) :
    (symplecticRankOne v).mulVec x =
      characteristicSymplecticForm x v • v := by
  funext i
  simp [symplecticRankOne, Matrix.mulVec, dotProduct,
    symplecticCovector, characteristicSymplecticForm,
    Fin.sum_univ_two]
  ring

theorem symplecticTransvection_smul
    (v x : IntegralLattice) (n : ℤ) :
    symplecticTransvection v n • x =
      x + (n * characteristicSymplecticForm x v) • v := by
  funext i
  fin_cases i <;>
    simp [symplecticTransvection, symplecticTransvectionMatrix,
      symplecticRankOne, symplecticCovector,
      characteristicSymplecticForm, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, zsmul_eq_mul] <;>
    ring

theorem symplecticTransvection_inv
    (v : IntegralLattice) (n : ℤ) :
    (symplecticTransvection v n)⁻¹ =
      symplecticTransvection v (-n) := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticTransvection, symplecticTransvectionMatrix,
      symplecticRankOne, symplecticCovector,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

theorem symplecticRankOne_conjugate
    (g : IntegralSymplecticGroup)
    (v : IntegralLattice) :
    g.1 * symplecticRankOne v * (g⁻¹).1 =
      symplecticRankOne (g • v) := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    symplecticRankOne_mulVec,
    symplecticRankOne_mulVec]
  change g •
      (characteristicSymplecticForm (g⁻¹ • x) v • v) =
    characteristicSymplecticForm x (g • v) • (g • v)
  have h :=
    characteristicSymplecticForm_smul g (g⁻¹ • x) v
  calc
    g • (characteristicSymplecticForm (g⁻¹ • x) v • v) =
        characteristicSymplecticForm (g⁻¹ • x) v • (g • v) := by
          exact smul_comm _ _ _
    _ = characteristicSymplecticForm x (g • v) • (g • v) := by
      rw [show characteristicSymplecticForm (g⁻¹ • x) v =
        characteristicSymplecticForm x (g • v) by simpa using h.symm]

@[simp]
theorem symplecticTransvection_coe_one
    (v : IntegralLattice) :
    (symplecticTransvection v 1 :
      Matrix SymplecticIndex SymplecticIndex ℤ) =
      1 + symplecticRankOne v := by
  ext i j
  simp [symplecticTransvection, symplecticTransvectionMatrix]

@[simp]
theorem symplecticTransvection_coe_neg_one
    (v : IntegralLattice) :
    (symplecticTransvection v (-1) :
      Matrix SymplecticIndex SymplecticIndex ℤ) =
      1 - symplecticRankOne v := by
  ext i j
  simp [symplecticTransvection, symplecticTransvectionMatrix,
    sub_eq_add_neg]

theorem symplecticRankOne_midpoint_of_commutes_conjugates
    (g : IntegralSymplecticGroup)
    (v : IntegralLattice)
    (hp : Commute g
      (symplecticTransvection v 1 * g *
        (symplecticTransvection v 1)⁻¹))
    (hm : Commute g
      (symplecticTransvection v (-1) * g *
        (symplecticTransvection v (-1))⁻¹)) :
    symplecticRankOne (g • v) +
        symplecticRankOne (g⁻¹ • v) =
      2 • symplecticRankOne v := by
  let B := g.1
  let R := symplecticRankOne v
  have hpM := congrArg Subtype.val hp.eq
  have hmM := congrArg Subtype.val hm.eq
  have hP :
      B * ((1 + R) * B * (1 - R)) =
        ((1 + R) * B * (1 - R)) * B := by
    simpa [B, R, symplecticTransvection_inv] using hpM
  have hM :
      B * ((1 - R) * B * (1 + R)) =
        ((1 - R) * B * (1 + R)) * B := by
    simpa [B, R, symplecticTransvection_inv] using hmM
  have hp0 :
      2 • (B * R * B) - B * B * R - R * B * B -
          B * R * B * R + R * B * R * B = 0 := by
    calc
      _ = B * ((1 + R) * B * (1 - R)) -
          ((1 + R) * B * (1 - R)) * B := by
            noncomm_ring
      _ = 0 := sub_eq_zero.mpr hP
  have hm0 :
      -(2 • (B * R * B)) + B * B * R + R * B * B -
          B * R * B * R + R * B * R * B = 0 := by
    calc
      _ = B * ((1 - R) * B * (1 + R)) -
          ((1 - R) * B * (1 + R)) * B := by
            noncomm_ring
      _ = 0 := sub_eq_zero.mpr hM
  have hlinear :
      2 • (B * R * B) = B * B * R + R * B * B := by
    ext i j
    have hpij := congrArg
      (fun M : Matrix SymplecticIndex SymplecticIndex ℤ =>
        M i j) hp0
    have hmij := congrArg
      (fun M : Matrix SymplecticIndex SymplecticIndex ℤ =>
        M i j) hm0
    change
      2 * (B * R * B) i j =
        (B * B * R) i j + (R * B * B) i j
    change
      2 * (B * R * B) i j -
          (B * B * R) i j - (R * B * B) i j -
          (B * R * B * R) i j +
          (R * B * R * B) i j = 0 at hpij
    change
      -(2 * (B * R * B) i j) +
          (B * B * R) i j + (R * B * B) i j -
          (B * R * B * R) i j +
          (R * B * R * B) i j = 0 at hmij
    linarith
  have hconj :
      B * R * (g⁻¹).1 + (g⁻¹).1 * R * B = 2 • R := by
    have hLB : (g⁻¹).1 * B = 1 := by
      have h := congrArg Subtype.val (inv_mul_cancel g)
      change (g⁻¹).1 * B =
        (1 : Matrix SymplecticIndex SymplecticIndex ℤ) at h
      exact h
    have hBR : B * (g⁻¹).1 = 1 := by
      have h := congrArg Subtype.val (mul_inv_cancel g)
      change B * (g⁻¹).1 =
        (1 : Matrix SymplecticIndex SymplecticIndex ℤ) at h
      exact h
    have hfirst :
        (g⁻¹).1 * (B * B * R) * (g⁻¹).1 =
          B * R * (g⁻¹).1 := by
      calc
        _ = ((g⁻¹).1 * B) * (B * R) * (g⁻¹).1 := by
          noncomm_ring
        _ = _ := by rw [hLB, one_mul]
    have hsecond :
        (g⁻¹).1 * (R * B * B) * (g⁻¹).1 =
          (g⁻¹).1 * R * B := by
      calc
        _ = (g⁻¹).1 * R * B * (B * (g⁻¹).1) := by
          noncomm_ring
        _ = _ := by rw [hBR, mul_one]
    have hscaled :
        (g⁻¹).1 * (2 • (B * R * B)) * (g⁻¹).1 =
          2 • R := by
      calc
        _ = 2 • (((g⁻¹).1 * B) * R *
            (B * (g⁻¹).1)) := by noncomm_ring
        _ = _ := by rw [hLB, hBR, one_mul, mul_one]
    calc
      B * R * (g⁻¹).1 + (g⁻¹).1 * R * B =
          (g⁻¹).1 * (B * B * R + R * B * B) *
            (g⁻¹).1 := by
              rw [mul_add, add_mul, hfirst, hsecond, add_comm]
      _ = (g⁻¹).1 * (2 • (B * R * B)) *
            (g⁻¹).1 := by rw [hlinear]
      _ = 2 • R := hscaled
  rw [symplecticRankOne_conjugate] at hconj
  have hinv :
      (g⁻¹).1 * symplecticRankOne v * g.1 =
        symplecticRankOne (g⁻¹ • v) := by
    simpa using symplecticRankOne_conjugate g⁻¹ v
  rw [hinv] at hconj
  exact hconj

def symmetricRankOne
    (v : IntegralLattice) :
    Matrix SymplecticIndex SymplecticIndex ℤ :=
  fun i j => v i * v j

theorem symplecticRankOne_mul_J
    (v : IntegralLattice) :
    symplecticRankOne v * Matrix.J (Fin 2) ℤ =
      symmetricRankOne v := by
  ext i j
  fin_cases j <;>
    simp [symplecticRankOne, symplecticCovector,
      symmetricRankOne, Matrix.J, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem symmetricRankOne_midpoint_of_midpoint
    (g : IntegralSymplecticGroup)
    (v : IntegralLattice)
    (h :
      symplecticRankOne (g • v) +
          symplecticRankOne (g⁻¹ • v) =
        2 • symplecticRankOne v) :
    symmetricRankOne (g • v) +
        symmetricRankOne (g⁻¹ • v) =
      2 • symmetricRankOne v := by
  have hJ := congrArg
    (fun M : Matrix SymplecticIndex SymplecticIndex ℤ =>
      M * Matrix.J (Fin 2) ℤ) h
  simpa only [two_nsmul, add_mul,
    symplecticRankOne_mul_J] using hJ

theorem smul_coordinate_eq_zero_of_midpoint
    (g : IntegralSymplecticGroup)
    (hmid : ∀ v : IntegralLattice,
      symplecticRankOne (g • v) +
          symplecticRankOne (g⁻¹ • v) =
        2 • symplecticRankOne v)
    (v : IntegralLattice) (i : SymplecticIndex)
    (hvi : v i = 0) :
    (g • v) i = 0 := by
  have h := symmetricRankOne_midpoint_of_midpoint g v (hmid v)
  have hii := congrArg
    (fun M : Matrix SymplecticIndex SymplecticIndex ℤ =>
      M i i) h
  change
    (g • v) i * (g • v) i +
        (g⁻¹ • v) i * (g⁻¹ • v) i =
      2 * (v i * v i) at hii
  rw [hvi] at hii
  nlinarith [sq_nonneg ((g⁻¹ • v) i)]

theorem smul_coordinate_eq_of_midpoint
    (g : IntegralSymplecticGroup)
    (hmid : ∀ v : IntegralLattice,
      symplecticRankOne (g • v) +
          symplecticRankOne (g⁻¹ • v) =
        2 • symplecticRankOne v)
    (v : IntegralLattice) (i j : SymplecticIndex)
    (hvij : v i = v j) :
    (g • v) i = (g • v) j := by
  have h := symmetricRankOne_midpoint_of_midpoint g v (hmid v)
  have hij := congrArg
    (fun M : Matrix SymplecticIndex SymplecticIndex ℤ =>
      M i i - M i j - M j i + M j j) h
  simp only [Matrix.add_apply,
    symmetricRankOne, two_nsmul] at hij
  rw [hvij] at hij
  nlinarith [sq_nonneg ((g⁻¹ • v) i - (g⁻¹ • v) j)]

theorem smul_integralBasisVector_of_midpoint
    (g : IntegralSymplecticGroup)
    (hmid : ∀ v : IntegralLattice,
      symplecticRankOne (g • v) +
          symplecticRankOne (g⁻¹ • v) =
        2 • symplecticRankOne v)
    (j : SymplecticIndex) :
    g • integralBasisVector j =
      ((g • integralBasisVector j) j) •
        integralBasisVector j := by
  funext i
  by_cases hji : j = i
  · subst i
    simp [integralBasisVector]
  · have hvzero : integralBasisVector j i = 0 := by
      simp [integralBasisVector, hji]
    have hgzero :=
      smul_coordinate_eq_zero_of_midpoint
        g hmid (integralBasisVector j) i hvzero
    calc
      (g • integralBasisVector j) i = 0 := hgzero
      _ = (((g • integralBasisVector j) j) •
          integralBasisVector j) i := by
        simp [integralBasisVector, hji]

theorem basis_diagonal_coeff_eq_of_midpoint
    (g : IntegralSymplecticGroup)
    (hmid : ∀ v : IntegralLattice,
      symplecticRankOne (g • v) +
          symplecticRankOne (g⁻¹ • v) =
        2 • symplecticRankOne v)
    (i j : SymplecticIndex) :
    (g • integralBasisVector i) i =
      (g • integralBasisVector j) j := by
  by_cases hij : i = j
  · subst j
    rfl
  · let v := integralBasisVector i + integralBasisVector j
    have hvij : v i = v j := by
      simp [v, integralBasisVector, hij, Ne.symm hij]
    have hcoord :=
      smul_coordinate_eq_of_midpoint g hmid v i j hvij
    dsimp [v] at hcoord
    change
      g.1.mulVec (integralBasisVector i + integralBasisVector j) i =
        g.1.mulVec (integralBasisVector i + integralBasisVector j) j at hcoord
    rw [Matrix.mulVec_add] at hcoord
    have hbi :=
      smul_integralBasisVector_of_midpoint g hmid i
    have hbj :=
      smul_integralBasisVector_of_midpoint g hmid j
    change g.1.mulVec (integralBasisVector i) =
      ((g • integralBasisVector i) i) •
        integralBasisVector i at hbi
    change g.1.mulVec (integralBasisVector j) =
      ((g • integralBasisVector j) j) •
        integralBasisVector j at hbj
    rw [hbi, hbj] at hcoord
    simpa [integralBasisVector, hij, Ne.symm hij,
      zsmul_eq_mul] using hcoord

def integralScalarMatrix (d : ℤ) :
    Matrix SymplecticIndex SymplecticIndex ℤ :=
  fun i j => if i = j then d else 0

theorem matrix_eq_scalar_of_midpoint
    (g : IntegralSymplecticGroup)
    (hmid : ∀ v : IntegralLattice,
      symplecticRankOne (g • v) +
          symplecticRankOne (g⁻¹ • v) =
        2 • symplecticRankOne v) :
    g.1 = integralScalarMatrix
      ((g • integralBasisVector (Sum.inl 0)) (Sum.inl 0)) := by
  let d := (g • integralBasisVector (Sum.inl 0)) (Sum.inl 0)
  ext i j
  have hbasis :=
    smul_integralBasisVector_of_midpoint g hmid j
  have hdiag :
      (g • integralBasisVector j) j = d := by
    exact basis_diagonal_coeff_eq_of_midpoint
      g hmid j (Sum.inl 0)
  rw [hdiag] at hbasis
  have hij := congrFun hbasis i
  have hentry :
      g.1 i j = (d • integralBasisVector j) i := by
    change
      g.1.mulVec (Pi.single j (1 : ℤ)) i =
        (d • integralBasisVector j) i at hij
    rw [Matrix.mulVec_single_one] at hij
    exact hij
  by_cases h : i = j
  · subst j
    simpa [integralScalarMatrix, integralBasisVector,
      Pi.single_apply, eq_comm, d, zsmul_eq_mul] using hentry
  · simpa [integralScalarMatrix, d, Pi.single_apply,
      integralBasisVector, eq_comm, h, zsmul_eq_mul] using hentry

def integralSymplecticNegOne :
    IntegralSymplecticGroup :=
  ⟨-(1 : Matrix SymplecticIndex SymplecticIndex ℤ),
    SymplecticGroup.neg_mem
      (Matrix.symplecticGroup (Fin 2) ℤ).one_mem⟩

theorem eq_one_or_neg_one_of_midpoint
    (g : IntegralSymplecticGroup)
    (hmid : ∀ v : IntegralLattice,
      symplecticRankOne (g • v) +
          symplecticRankOne (g⁻¹ • v) =
        2 • symplecticRankOne v) :
    g = 1 ∨ g = integralSymplecticNegOne := by
  let e : SymplecticIndex := Sum.inl 0
  let f : SymplecticIndex := Sum.inr 0
  let d := (g • integralBasisVector e) e
  have he :=
    smul_integralBasisVector_of_midpoint g hmid e
  change g • integralBasisVector e =
    d • integralBasisVector e at he
  have hf :=
    smul_integralBasisVector_of_midpoint g hmid f
  have hdf :
      (g • integralBasisVector f) f = d :=
    basis_diagonal_coeff_eq_of_midpoint g hmid f e
  rw [hdf] at hf
  have hform :=
    characteristicSymplecticForm_smul g
      (integralBasisVector e) (integralBasisVector f)
  rw [he, hf] at hform
  have hd : d ^ 2 = 1 := by
    simp [characteristicSymplecticForm, integralBasisVector,
      Pi.single_apply, e, f] at hform
    nlinarith
  have hmatrix := matrix_eq_scalar_of_midpoint g hmid
  rcases sq_eq_one_iff.mp hd with hd1 | hdm1
  · left
    apply Subtype.ext
    rw [hmatrix]
    ext i j
    simp [integralScalarMatrix, d, e, hd1, Matrix.one_apply]
  · right
    apply Subtype.ext
    rw [hmatrix]
    ext i j
    by_cases hij : i = j
    · simp [integralSymplecticNegOne, integralScalarMatrix,
        d, e, hdm1, hij]
    · simp [integralSymplecticNegOne, integralScalarMatrix,
        hij]

theorem eq_one_or_neg_one_of_commutes_all_conjugates
    (g : IntegralSymplecticGroup)
    (hcomm : ∀ q : IntegralSymplecticGroup,
      Commute g (q * g * q⁻¹)) :
    g = 1 ∨ g = integralSymplecticNegOne := by
  apply eq_one_or_neg_one_of_midpoint g
  intro v
  exact symplecticRankOne_midpoint_of_commutes_conjugates
    g v
      (hcomm (symplecticTransvection v 1))
      (hcomm (symplecticTransvection v (-1)))

theorem integralSymplecticNegOne_smul
    (v : IntegralLattice) :
    integralSymplecticNegOne • v = -v := by
  funext i
  simp [integralSymplecticNegOne]

theorem cocycleExtension_kernel_commute
    {c : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice}
    (x y : CocycleExtension c)
    (hx : x.snd = 1) (hy : y.snd = 1) :
    Commute x y := by
  apply CocycleExtension.ext
  · simp only [CocycleExtension.mul_fst]
    rw [hx, hy]
    simp only [c.one_left, add_zero]
    funext i
    change x.fst i +
        (1 : Matrix SymplecticIndex SymplecticIndex ℤ).mulVec y.fst i =
      y.fst i +
        (1 : Matrix SymplecticIndex SymplecticIndex ℤ).mulVec x.fst i
    simp only [Matrix.one_mulVec]
    ring
  · simp [hx, hy]

theorem cocycleExtension_conjugate_kernel_snd
    {c : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice}
    (z x : CocycleExtension c)
    (hx : x.snd = 1) :
    (z * x * z⁻¹).snd = 1 := by
  simp [hx]

theorem kernel_commutator
    {c : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice}
    (a : IntegralLattice) (x : CocycleExtension c) :
    ({ fst := a, snd := (1 : IntegralSymplecticGroup) } :
        CocycleExtension c) * x *
          ({ fst := a, snd := (1 : IntegralSymplecticGroup) } :
            CocycleExtension c)⁻¹ * x⁻¹ =
      ({ fst := a - x.snd • a,
          snd := (1 : IntegralSymplecticGroup) } :
        CocycleExtension c) := by
  rw [kernel_conjugation]
  apply (mul_right_cancel_iff (a := x)).mp
  rw [mul_assoc, inv_mul_cancel, mul_one]
  apply CocycleExtension.ext
  · simp only [CocycleExtension.mul_fst]
    rw [c.one_left]
    simp only [add_zero]
    funext i
    change x.fst i + (a i - (x.snd • a) i) =
      (a i - (x.snd • a) i) +
        (1 : Matrix SymplecticIndex SymplecticIndex ℤ).mulVec x.fst i
    simp only [Matrix.one_mulVec]
    ring
  · simp




theorem cocycleExtension_equiv_maps_kernel
    {c d : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice}
    (f : CocycleExtension c ≃* CocycleExtension d)
    (x : CocycleExtension c) (hx : x.snd = 1) :
    (f x).snd = 1 := by
  let y : CocycleExtension d := f x
  have hy_commutes_conjugates :
      ∀ q : IntegralSymplecticGroup,
        Commute y
          (({ fst := 0, snd := q } : CocycleExtension d) * y *
            ({ fst := 0, snd := q } : CocycleExtension d)⁻¹) := by
    intro q
    let z : CocycleExtension d := { fst := 0, snd := q }
    let u : CocycleExtension c := f.symm z
    let xq : CocycleExtension c := u * x * u⁻¹
    have hxq : xq.snd = 1 :=
      cocycleExtension_conjugate_kernel_snd u x hx
    have hsource : Commute x xq :=
      cocycleExtension_kernel_commute x xq hx hxq
    have hmapped := hsource.map f.toMonoidHom
    simpa [y, xq, u, z] using hmapped
  have hy_snd_commutes_conjugates :
      ∀ q : IntegralSymplecticGroup,
        Commute y.snd (q * y.snd * q⁻¹) := by
    intro q
    have hmapped :=
      (hy_commutes_conjugates q).map (CocycleExtension.rightHom d)
    simpa using hmapped
  rcases eq_one_or_neg_one_of_commutes_all_conjugates
      y.snd hy_snd_commutes_conjugates with hone | hneg
  · simpa [y] using hone
  · exfalso
    let a : IntegralLattice := integralBasisVector (Sum.inl 0)
    let k : CocycleExtension d :=
      { fst := a, snd := (1 : IntegralSymplecticGroup) }
    let u : CocycleExtension c := f.symm k
    let w : CocycleExtension c := u * x * u⁻¹ * x⁻¹
    have hw : w.snd = 1 := by
      simp [w, hx]
    have hsource : Commute x w :=
      cocycleExtension_kernel_commute x w hx hw
    have hmapped := hsource.map f.toMonoidHom
    have hcomm :
        Commute y
          ({ fst := a - y.snd • a,
             snd := (1 : IntegralSymplecticGroup) } :
            CocycleExtension d) := by
      simpa [y, w, u, k, kernel_commutator] using hmapped
    let b : IntegralLattice := a - y.snd • a
    have hfixedConjugate :
        y *
            ({ fst := b, snd := (1 : IntegralSymplecticGroup) } :
              CocycleExtension d) *
              y⁻¹ =
          ({ fst := b, snd := (1 : IntegralSymplecticGroup) } :
            CocycleExtension d) := by
      calc
        y *
              ({ fst := b, snd := (1 : IntegralSymplecticGroup) } :
                CocycleExtension d) *
                y⁻¹ =
            ({ fst := b, snd := (1 : IntegralSymplecticGroup) } :
              CocycleExtension d) * y * y⁻¹ := by
                rw [hcomm.eq]
        _ = _ := by simp
    have hstruct :
        ({ fst := y.snd • b,
           snd := (1 : IntegralSymplecticGroup) } :
          CocycleExtension d) =
        ({ fst := b,
           snd := (1 : IntegralSymplecticGroup) } :
          CocycleExtension d) :=
      (extension_conjugation_kernel y b).symm.trans hfixedConjugate
    have hfixed : y.snd • b = b :=
      congr_arg CocycleExtension.fst hstruct
    dsimp [b] at hfixed
    rw [hneg, integralSymplecticNegOne_smul,
      integralSymplecticNegOne_smul] at hfixed
    have hcoordinate := congr_fun hfixed (Sum.inl 0)
    simp [a, integralBasisVector] at hcoordinate



theorem cocycleExtension_equiv_preserves_kernel
    {c d : NormalizedAddCocycle
      IntegralSymplecticGroup IntegralLattice}
    (f : CocycleExtension c ≃* CocycleExtension d)
    (x : CocycleExtension c) :
    x.snd = 1 ↔ (f x).snd = 1 := by
  constructor
  · exact cocycleExtension_equiv_maps_kernel f x
  · intro hx
    have hback :=
      cocycleExtension_equiv_maps_kernel f.symm (f x) hx
    simpa using hback



theorem gammaKernel_is_characteristic_proved
    (f : IntegralSymplecticCocycleInput.GammaZero ≃*
      integralSymplecticCocycleInput.GammaOne) :
    CocycleExtension.PreservesKernel
      integralSymplecticCocycleInput.twoCocycle f :=
  cocycleExtension_equiv_preserves_kernel f

end ConnesRigidity
