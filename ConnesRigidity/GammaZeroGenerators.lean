
import ConnesRigidity.PropertyTSumOfSquares
import ConnesRigidity.CrossedClosure
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

namespace ConnesRigidity

open Matrix
open scoped MatrixGroups

def symplecticRootA12 : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else if i = j then 1 else 0

def symplecticRootA12Dual : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = 1 ∧ j = 0 then -1 else if i = j then 1 else 0

def symplecticRootA21 : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = 1 ∧ j = 0 then 1 else if i = j then 1 else 0

def symplecticRootA21Dual : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = 0 ∧ j = 1 then -1 else if i = j then 1 else 0

def symplecticRootD12Matrix : Matrix SymplecticIndex SymplecticIndex ℤ :=
  Matrix.fromBlocks symplecticRootA12 0 0 symplecticRootA12Dual

def symplecticRootD21Matrix : Matrix SymplecticIndex SymplecticIndex ℤ :=
  Matrix.fromBlocks symplecticRootA21 0 0 symplecticRootA21Dual

private theorem symplecticRootD12Matrix_mem :
    symplecticRootD12Matrix ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [symplecticRootD12Matrix, symplecticRootA12,
      symplecticRootA12Dual, Matrix.mul_apply, Matrix.J, Matrix.fromBlocks]

private theorem symplecticRootD21Matrix_mem :
    symplecticRootD21Matrix ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [symplecticRootD21Matrix, symplecticRootA21,
      symplecticRootA21Dual, Matrix.mul_apply, Matrix.J, Matrix.fromBlocks]

def symplecticRootD12 : IntegralSymplecticGroup :=
  ⟨symplecticRootD12Matrix, symplecticRootD12Matrix_mem⟩

def symplecticRootD21 : IntegralSymplecticGroup :=
  ⟨symplecticRootD21Matrix, symplecticRootD21Matrix_mem⟩

def symplecticCrossShearBlock : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = j then 0 else 1

theorem symplecticCrossShearBlock_symmetric :
    symplecticCrossShearBlock.transpose = symplecticCrossShearBlock := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symplecticCrossShearBlock, Matrix.transpose_apply]

def upperCrossTransvection : IntegralSymplecticGroup :=
  upperShear symplecticCrossShearBlock symplecticCrossShearBlock_symmetric

def lowerCrossTransvection : IntegralSymplecticGroup :=
  lowerShear symplecticCrossShearBlock symplecticCrossShearBlock_symmetric

private theorem matrix_int_smul_symmetric
    (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.transpose = B) (n : ℤ) :
    (n • B).transpose = n • B := by
  ext i j
  have hij := congrFun (congrFun hB i) j
  change n * B j i = n * B i j
  rw [show B j i = B i j by simpa [Matrix.transpose_apply] using hij]

@[simp]
private theorem intCast_matrix_fin_two_apply
    (n : ℤ) (i j : Fin 2) :
    (n : Matrix (Fin 2) (Fin 2) ℤ) i j =
      if i = j then n else 0 := by
  rw [← zsmul_one]
  simp [Matrix.one_apply]

private theorem upperShear_mul
    (B C : Matrix (Fin 2) (Fin 2) ℤ)
    (hB : B.transpose = B) (hC : C.transpose = C) :
    upperShear B hB * upperShear C hC =
      upperShear (B + C) (by rw [Matrix.transpose_add, hB, hC]) := by
  apply Subtype.ext
  simp [upperShear, Matrix.fromBlocks_multiply, add_comm]

private theorem upperShear_inv
    (B : Matrix (Fin 2) (Fin 2) ℤ)
    (hB : B.transpose = B) :
    (upperShear B hB)⁻¹ =
      upperShear (-B) (by rw [Matrix.transpose_neg, hB]) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  simp [upperShear, Matrix.fromBlocks_multiply]

private theorem upperShear_zpow
    (B : Matrix (Fin 2) (Fin 2) ℤ)
    (hB : B.transpose = B) (n : ℤ) :
    (upperShear B hB) ^ n =
      upperShear (n • B) (matrix_int_smul_symmetric B hB n) := by
  induction n with
  | zero =>
      apply Subtype.ext
      simp [upperShear]
  | succ n hn =>
      rw [_root_.zpow_add, zpow_one, hn, upperShear_mul]
      apply Subtype.ext
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp only [upperShear, fromBlocks, zsmul_eq_mul, Int.cast_natCast,
          of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.add_apply,
          Matrix.zero_apply, Int.cast_add, Int.cast_one]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  | pred n hn =>
      rw [_root_.zpow_sub, zpow_one, hn, upperShear_inv, upperShear_mul]
      apply Subtype.ext
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp only [upperShear, fromBlocks, neg_smul, zsmul_eq_mul,
          Int.cast_natCast, of_apply, Sum.elim_inl, Sum.elim_inr,
          Matrix.add_apply, Matrix.neg_apply, Matrix.zero_apply,
          Int.cast_sub, Int.cast_neg, Int.cast_one]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def symplecticPlaneMatrix (k : Fin 2)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Matrix SymplecticIndex SymplecticIndex ℤ
  | Sum.inl i, Sum.inl j =>
      if i = k then if j = k then A 0 0 else 0
      else if i = j then 1 else 0
  | Sum.inl i, Sum.inr j =>
      if i = k ∧ j = k then A 0 1 else 0
  | Sum.inr i, Sum.inl j =>
      if i = k ∧ j = k then A 1 0 else 0
  | Sum.inr i, Sum.inr j =>
      if i = k then if j = k then A 1 1 else 0
      else if i = j then 1 else 0

private theorem symplecticPlaneMatrix_one (k : Fin 2) :
    symplecticPlaneMatrix k 1 = 1 := by
  ext i j
  fin_cases k <;> rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [symplecticPlaneMatrix, Matrix.one_apply] <;> simp

private theorem symplecticPlaneMatrix_mul (k : Fin 2)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    symplecticPlaneMatrix k (A * B) =
      symplecticPlaneMatrix k A * symplecticPlaneMatrix k B := by
  ext i j
  fin_cases k <;> rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [symplecticPlaneMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private theorem symplecticPlaneMatrix_mem (k : Fin 2)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    symplecticPlaneMatrix k A ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  rw [SymplecticGroup.mem_iff]
  ext i j
  fin_cases k <;> rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [symplecticPlaneMatrix, Matrix.mul_apply, Matrix.J,
      Matrix.fromBlocks] <;>
    nlinarith [hdet]

def symplecticPlaneEmbedding (k : Fin 2) :
    Matrix.SpecialLinearGroup (Fin 2) ℤ →* IntegralSymplecticGroup where
  toFun A := ⟨symplecticPlaneMatrix k A, symplecticPlaneMatrix_mem k A⟩
  map_one' := Subtype.ext (symplecticPlaneMatrix_one k)
  map_mul' A B := Subtype.ext (symplecticPlaneMatrix_mul k A B)

def sl2InverseTransposeMatrix
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  !![A 1 1, -A 1 0; -A 0 1, A 0 0]

def symplecticDiagonalMatrix
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Matrix SymplecticIndex SymplecticIndex ℤ :=
  Matrix.fromBlocks A 0 0 (sl2InverseTransposeMatrix A)

private theorem sl2InverseTransposeMatrix_one :
    sl2InverseTransposeMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sl2InverseTransposeMatrix, Matrix.one_apply]

private theorem sl2InverseTransposeMatrix_mul
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    sl2InverseTransposeMatrix (A * B) =
      sl2InverseTransposeMatrix A * sl2InverseTransposeMatrix B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2InverseTransposeMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

private theorem symplecticDiagonalMatrix_one :
    symplecticDiagonalMatrix 1 = 1 := by
  rw [symplecticDiagonalMatrix, sl2InverseTransposeMatrix_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks]

private theorem symplecticDiagonalMatrix_mul
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    symplecticDiagonalMatrix (A * B) =
      symplecticDiagonalMatrix A * symplecticDiagonalMatrix B := by
  rw [symplecticDiagonalMatrix, symplecticDiagonalMatrix,
    symplecticDiagonalMatrix, Matrix.fromBlocks_multiply,
    sl2InverseTransposeMatrix_mul]
  simp

private theorem symplecticDiagonalMatrix_mem
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    symplecticDiagonalMatrix A ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [symplecticDiagonalMatrix, SymplecticGroup.fromBlocks_mem_iff]
  simp only [Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul,
    true_and, sub_zero]
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2InverseTransposeMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [hdet]

def symplecticDiagonalEmbedding :
    Matrix.SpecialLinearGroup (Fin 2) ℤ →* IntegralSymplecticGroup where
  toFun A := ⟨symplecticDiagonalMatrix A, symplecticDiagonalMatrix_mem A⟩
  map_one' := Subtype.ext symplecticDiagonalMatrix_one
  map_mul' A B := Subtype.ext (symplecticDiagonalMatrix_mul A B)

set_option maxRecDepth 10000 in

theorem exists_sl2_mulVec_eq_gcd (a b : ℤ) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      A.1.mulVec ![a, b] = ![(Int.gcd a b : ℤ), 0] := by
  by_cases hd : Int.gcd a b = 0
  · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp hd
    exact ⟨1, by simp⟩
  · have hdpos : 0 < Int.gcd a b := Nat.pos_of_ne_zero hd
    obtain ⟨a', b', hab, ha, hb⟩ := Int.exists_gcd_one hdpos
    let d : ℤ := (Int.gcd a b : ℤ)
    have ha' : a = a' * d := by simpa [d] using ha
    have hb' : b = b' * d := by simpa [d] using hb
    have hbezout :
        (1 : ℤ) =
          a' * Int.gcdA a' b' + b' * Int.gcdB a' b' := by
      simpa [hab] using Int.gcd_eq_gcd_ab a' b'
    let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
      ⟨!![Int.gcdA a' b', Int.gcdB a' b'; -b', a'], by
        rw [Matrix.det_fin_two]
        dsimp
        nlinarith [hbezout]⟩
    refine ⟨A, ?_⟩
    ext i
    fin_cases i
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      dsimp only [A]
      change
        Int.gcdA a' b' * a + Int.gcdB a' b' * b =
          (Int.gcd a b : ℤ)
      change
        Int.gcdA a' b' * a + Int.gcdB a' b' * b = d
      rw [ha', hb']
      nlinarith [hbezout]
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      dsimp only [A]
      change -b' * a + a' * b = 0
      rw [ha', hb']
      ring

def symplecticFirstColumn
    (g : IntegralSymplecticGroup) : IntegralLattice :=
  fun i => g.1 i (Sum.inl 0)

@[simp]
theorem symplecticFirstColumn_mul
    (g h : IntegralSymplecticGroup) :
    symplecticFirstColumn (g * h) = g • symplecticFirstColumn h :=
  rfl

@[simp]
theorem symplecticPlaneEmbedding_smul_inl_self
    (k : Fin 2) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (v : IntegralLattice) :
    (symplecticPlaneEmbedding k A • v) (Sum.inl k) =
      A 0 0 * v (Sum.inl k) + A 0 1 * v (Sum.inr k) := by
  fin_cases k <;>
    simp [symplecticPlaneEmbedding, symplecticPlaneMatrix,
      Matrix.mulVec, dotProduct]

@[simp]
theorem symplecticPlaneEmbedding_smul_inr_self
    (k : Fin 2) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (v : IntegralLattice) :
    (symplecticPlaneEmbedding k A • v) (Sum.inr k) =
      A 1 0 * v (Sum.inl k) + A 1 1 * v (Sum.inr k) := by
  fin_cases k <;>
    simp [symplecticPlaneEmbedding, symplecticPlaneMatrix,
      Matrix.mulVec, dotProduct]

@[simp]
theorem symplecticPlaneEmbedding_smul_inl_other
    (k j : Fin 2) (hjk : j ≠ k)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (v : IntegralLattice) :
    (symplecticPlaneEmbedding k A • v) (Sum.inl j) =
      v (Sum.inl j) := by
  fin_cases k <;> fin_cases j <;>
    simp_all [symplecticPlaneEmbedding, symplecticPlaneMatrix,
      Matrix.mulVec, dotProduct]

@[simp]
theorem symplecticPlaneEmbedding_smul_inr_other
    (k j : Fin 2) (hjk : j ≠ k)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (v : IntegralLattice) :
    (symplecticPlaneEmbedding k A • v) (Sum.inr j) =
      v (Sum.inr j) := by
  fin_cases k <;> fin_cases j <;>
    simp_all [symplecticPlaneEmbedding, symplecticPlaneMatrix,
      Matrix.mulVec, dotProduct]

@[simp]
theorem symplecticDiagonalEmbedding_smul_inl
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (v : IntegralLattice) (i : Fin 2) :
    (symplecticDiagonalEmbedding A • v) (Sum.inl i) =
      A i 0 * v (Sum.inl 0) + A i 1 * v (Sum.inl 1) := by
  fin_cases i <;>
    simp [symplecticDiagonalEmbedding, symplecticDiagonalMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.fromBlocks]

@[simp]
theorem symplecticDiagonalEmbedding_smul_inr
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (v : IntegralLattice) (i : Fin 2) :
    (symplecticDiagonalEmbedding A • v) (Sum.inr i) =
      sl2InverseTransposeMatrix A i 0 * v (Sum.inr 0) +
        sl2InverseTransposeMatrix A i 1 * v (Sum.inr 1) := by
  fin_cases i <;>
    simp [symplecticDiagonalEmbedding, symplecticDiagonalMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.fromBlocks]

def positiveElementarySymplecticGeneratorList :
    List IntegralSymplecticGroup :=
  [upperTransvectionE1, upperTransvectionE2, upperCrossTransvection,
    transvectionF1, transvectionF2, lowerCrossTransvection,
    symplecticRootD12, symplecticRootD21]

noncomputable def elementarySymplecticGenerators :
    Finset IntegralSymplecticGroup :=
  let positive := positiveElementarySymplecticGeneratorList.toFinset
  positive ∪ positive.image Inv.inv

noncomputable def elementarySymplecticSubgroup :
    Subgroup IntegralSymplecticGroup :=
  Subgroup.closure (elementarySymplecticGenerators :
    Set IntegralSymplecticGroup)

private theorem positiveElementarySymplecticGenerator_mem
    {g : IntegralSymplecticGroup}
    (hg : g ∈ positiveElementarySymplecticGeneratorList) :
    g ∈ elementarySymplecticSubgroup := by
  apply Subgroup.subset_closure
  change g ∈ positiveElementarySymplecticGeneratorList.toFinset ∪
    positiveElementarySymplecticGeneratorList.toFinset.image Inv.inv
  exact Finset.mem_union_left _
    (List.mem_toFinset.mpr hg)

private theorem upperTransvectionE1_mem :
    upperTransvectionE1 ∈ elementarySymplecticSubgroup :=
  positiveElementarySymplecticGenerator_mem (by simp
    [positiveElementarySymplecticGeneratorList])

private theorem upperTransvectionE2_mem :
    upperTransvectionE2 ∈ elementarySymplecticSubgroup :=
  positiveElementarySymplecticGenerator_mem (by simp
    [positiveElementarySymplecticGeneratorList])

private theorem transvectionF1_mem :
    transvectionF1 ∈ elementarySymplecticSubgroup :=
  positiveElementarySymplecticGenerator_mem (by simp
    [positiveElementarySymplecticGeneratorList])

private theorem transvectionF2_mem :
    transvectionF2 ∈ elementarySymplecticSubgroup :=
  positiveElementarySymplecticGenerator_mem (by simp
    [positiveElementarySymplecticGeneratorList])

private theorem upperCrossTransvection_mem :
    upperCrossTransvection ∈ elementarySymplecticSubgroup :=
  positiveElementarySymplecticGenerator_mem (by simp
    [positiveElementarySymplecticGeneratorList])

private theorem symplecticRootD12_mem :
    symplecticRootD12 ∈ elementarySymplecticSubgroup :=
  positiveElementarySymplecticGenerator_mem (by simp
    [positiveElementarySymplecticGeneratorList])

private theorem symplecticRootD21_mem :
    symplecticRootD21 ∈ elementarySymplecticSubgroup :=
  positiveElementarySymplecticGenerator_mem (by simp
    [positiveElementarySymplecticGeneratorList])

private theorem upperShear_mem
    (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.transpose = B) :
    upperShear B hB ∈ elementarySymplecticSubgroup := by
  have h10 : B 1 0 = B 0 1 := by
    have h := congrFun (congrFun hB 0) 1
    simpa [Matrix.transpose_apply] using h
  have hdecomp :
      B =
        B 0 0 • lowerShearB1 +
          B 0 1 • symplecticCrossShearBlock +
            B 1 1 • lowerShearB2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerShearB1, lowerShearB2, symplecticCrossShearBlock,
        Matrix.mul_apply, Fin.sum_univ_two, h10,
        intCast_matrix_fin_two_apply]
  have hfactor :
      upperShear B hB =
        upperTransvectionE1 ^ (B 0 0) *
          upperCrossTransvection ^ (B 0 1) *
            upperTransvectionE2 ^ (B 1 1) := by
    rw [upperTransvectionE1, upperCrossTransvection,
      upperTransvectionE2, upperShear_zpow, upperShear_zpow,
      upperShear_zpow, upperShear_mul, upperShear_mul]
    apply Subtype.ext
    simpa [upperShear] using hdecomp
  rw [hfactor]
  exact elementarySymplecticSubgroup.mul_mem
    (elementarySymplecticSubgroup.mul_mem
      (elementarySymplecticSubgroup.zpow_mem upperTransvectionE1_mem _)
      (elementarySymplecticSubgroup.zpow_mem upperCrossTransvection_mem _))
    (elementarySymplecticSubgroup.zpow_mem upperTransvectionE2_mem _)

def sl2LowerUnit : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, 0; 1, 1], by norm_num [Matrix.det_fin_two]⟩

private theorem modularS_factorization :
    ModularGroup.S =
      ModularGroup.T⁻¹ * sl2LowerUnit * ModularGroup.T⁻¹ := by
  decide

private theorem symplecticPlaneEmbedding_T (k : Fin 2) :
    symplecticPlaneEmbedding k ModularGroup.T =
      if k = 0 then upperTransvectionE1 else upperTransvectionE2 := by
  apply Subtype.ext
  fin_cases k <;>
    ext i j <;>
    rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [symplecticPlaneEmbedding, symplecticPlaneMatrix,
      ModularGroup.T, upperTransvectionE1, upperTransvectionE2,
      upperShear, lowerShearB1, lowerShearB2, Matrix.fromBlocks]

private theorem symplecticPlaneEmbedding_lowerUnit (k : Fin 2) :
    symplecticPlaneEmbedding k sl2LowerUnit =
      if k = 0 then transvectionF1 else transvectionF2 := by
  apply Subtype.ext
  fin_cases k <;>
    ext i j <;>
    rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [symplecticPlaneEmbedding, symplecticPlaneMatrix,
      sl2LowerUnit, transvectionF1, transvectionF2, lowerShear,
      lowerShearB1, lowerShearB2, Matrix.fromBlocks]

private theorem symplecticPlaneEmbedding_S (k : Fin 2) :
    symplecticPlaneEmbedding k ModularGroup.S =
      if k = 0 then
        upperTransvectionE1⁻¹ * transvectionF1 * upperTransvectionE1⁻¹
      else
        upperTransvectionE2⁻¹ * transvectionF2 * upperTransvectionE2⁻¹ := by
  rw [modularS_factorization, map_mul, map_mul, map_inv,
    symplecticPlaneEmbedding_T, symplecticPlaneEmbedding_lowerUnit]
  split <;> simp_all

private theorem symplecticDiagonalEmbedding_T :
    symplecticDiagonalEmbedding ModularGroup.T = symplecticRootD12 := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [symplecticDiagonalEmbedding, symplecticDiagonalMatrix,
      sl2InverseTransposeMatrix, ModularGroup.T, symplecticRootD12,
      symplecticRootD12Matrix, symplecticRootA12,
      symplecticRootA12Dual, Matrix.fromBlocks]

private theorem symplecticDiagonalEmbedding_lowerUnit :
    symplecticDiagonalEmbedding sl2LowerUnit = symplecticRootD21 := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [symplecticDiagonalEmbedding, symplecticDiagonalMatrix,
      sl2InverseTransposeMatrix, sl2LowerUnit, symplecticRootD21,
      symplecticRootD21Matrix, symplecticRootA21,
      symplecticRootA21Dual, Matrix.fromBlocks]

private theorem symplecticDiagonalEmbedding_S :
    symplecticDiagonalEmbedding ModularGroup.S =
      symplecticRootD12⁻¹ * symplecticRootD21 * symplecticRootD12⁻¹ := by
  rw [modularS_factorization, map_mul, map_mul, map_inv,
    symplecticDiagonalEmbedding_T, symplecticDiagonalEmbedding_lowerUnit]

private theorem symplecticPlaneEmbedding_mem (k : Fin 2)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    symplecticPlaneEmbedding k A ∈ elementarySymplecticSubgroup := by
  let H := elementarySymplecticSubgroup.comap (symplecticPlaneEmbedding k)
  have hST : ({ModularGroup.S, ModularGroup.T} :
      Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) ⊆ H := by
    intro x hx
    rcases hx with (rfl | hx)
    · change symplecticPlaneEmbedding k ModularGroup.S ∈
        elementarySymplecticSubgroup
      rw [symplecticPlaneEmbedding_S]
      split
      · exact elementarySymplecticSubgroup.mul_mem
          (elementarySymplecticSubgroup.mul_mem
            (elementarySymplecticSubgroup.inv_mem upperTransvectionE1_mem)
            transvectionF1_mem)
          (elementarySymplecticSubgroup.inv_mem upperTransvectionE1_mem)
      · exact elementarySymplecticSubgroup.mul_mem
          (elementarySymplecticSubgroup.mul_mem
            (elementarySymplecticSubgroup.inv_mem upperTransvectionE2_mem)
            transvectionF2_mem)
          (elementarySymplecticSubgroup.inv_mem upperTransvectionE2_mem)
    · have hxT : x = ModularGroup.T := by simpa using hx
      subst x
      change symplecticPlaneEmbedding k ModularGroup.T ∈
        elementarySymplecticSubgroup
      rw [symplecticPlaneEmbedding_T]
      split
      · exact upperTransvectionE1_mem
      · exact upperTransvectionE2_mem
  have hclosure :
      Subgroup.closure ({ModularGroup.S, ModularGroup.T} :
        Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) ≤ H :=
    (Subgroup.closure_le H).2 hST
  change symplecticPlaneEmbedding k A ∈ elementarySymplecticSubgroup
  exact hclosure (by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top A)

private theorem symplecticDiagonalEmbedding_mem
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    symplecticDiagonalEmbedding A ∈ elementarySymplecticSubgroup := by
  let H := elementarySymplecticSubgroup.comap symplecticDiagonalEmbedding
  have hST : ({ModularGroup.S, ModularGroup.T} :
      Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) ⊆ H := by
    intro x hx
    rcases hx with (rfl | hx)
    · change symplecticDiagonalEmbedding ModularGroup.S ∈
        elementarySymplecticSubgroup
      rw [symplecticDiagonalEmbedding_S]
      exact elementarySymplecticSubgroup.mul_mem
        (elementarySymplecticSubgroup.mul_mem
          (elementarySymplecticSubgroup.inv_mem symplecticRootD12_mem)
          symplecticRootD21_mem)
        (elementarySymplecticSubgroup.inv_mem symplecticRootD12_mem)
    · have hxT : x = ModularGroup.T := by simpa using hx
      subst x
      change symplecticDiagonalEmbedding ModularGroup.T ∈
        elementarySymplecticSubgroup
      rw [symplecticDiagonalEmbedding_T]
      exact symplecticRootD12_mem
  have hclosure :
      Subgroup.closure ({ModularGroup.S, ModularGroup.T} :
        Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) ≤ H :=
    (Subgroup.closure_le H).2 hST
  change symplecticDiagonalEmbedding A ∈ elementarySymplecticSubgroup
  exact hclosure (by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top A)

theorem exists_elementary_mul_firstColumn_eq_basis
    (g : IntegralSymplecticGroup) :
    ∃ p : IntegralSymplecticGroup,
      p ∈ elementarySymplecticSubgroup ∧
      symplecticFirstColumn (p * g) =
        Pi.single (Sum.inl 0) 1 := by
  let v0 := symplecticFirstColumn g
  let d1 : ℤ := (Int.gcd (v0 (Sum.inl 0)) (v0 (Sum.inr 0)) : ℤ)
  obtain ⟨A1, hA1⟩ :=
    exists_sl2_mulVec_eq_gcd (v0 (Sum.inl 0)) (v0 (Sum.inr 0))
  let p1 := symplecticPlaneEmbedding 0 A1
  let v1 := p1 • v0
  have h1e1 : v1 (Sum.inl 0) = d1 := by
    have h := congrFun hA1 0
    simpa [v1, p1, d1, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] using h
  have h1f1 : v1 (Sum.inr 0) = 0 := by
    have h := congrFun hA1 1
    simpa [v1, p1, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] using h
  have h1e2 : v1 (Sum.inl 1) = v0 (Sum.inl 1) := by
    simp [v1, p1]
  have h1f2 : v1 (Sum.inr 1) = v0 (Sum.inr 1) := by
    simp [v1, p1]
  let d2 : ℤ := (Int.gcd (v1 (Sum.inl 1)) (v1 (Sum.inr 1)) : ℤ)
  obtain ⟨A2, hA2⟩ :=
    exists_sl2_mulVec_eq_gcd (v1 (Sum.inl 1)) (v1 (Sum.inr 1))
  let p2 := symplecticPlaneEmbedding 1 A2
  let v2 := p2 • v1
  have h2e1 : v2 (Sum.inl 0) = d1 := by
    simp [v2, p2, h1e1]
  have h2f1 : v2 (Sum.inr 0) = 0 := by
    simp [v2, p2, h1f1]
  have h2e2 : v2 (Sum.inl 1) = d2 := by
    have h := congrFun hA2 0
    simpa [v2, p2, d2, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] using h
  have h2f2 : v2 (Sum.inr 1) = 0 := by
    have h := congrFun hA2 1
    simpa [v2, p2, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] using h
  let d3 : ℤ := (Int.gcd d1 d2 : ℤ)
  obtain ⟨A3, hA3⟩ := exists_sl2_mulVec_eq_gcd d1 d2
  let p3 := symplecticDiagonalEmbedding A3
  let v3 := p3 • v2
  have h3e1 : v3 (Sum.inl 0) = d3 := by
    have h := congrFun hA3 0
    simpa [v3, p3, d3, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, h2e1, h2e2] using h
  have h3e2 : v3 (Sum.inl 1) = 0 := by
    have h := congrFun hA3 1
    simpa [v3, p3, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, h2e1, h2e2] using h
  have h3f1 : v3 (Sum.inr 0) = 0 := by
    simp [v3, p3, h2f1, h2f2]
  have h3f2 : v3 (Sum.inr 1) = 0 := by
    simp [v3, p3, h2f1, h2f2]
  let p := p3 * p2 * p1
  let h := p * g
  have hfirst_d3 :
      symplecticFirstColumn h = Pi.single (Sum.inl 0) d3 := by
    have hv : symplecticFirstColumn h = v3 := by
      simp [h, p, v3, v2, v1, p3, p2, p1, v0, mul_smul]
    rw [hv]
    funext i
    rcases i with i | i <;> fin_cases i <;>
      simp [Pi.single, h3e1, h3e2, h3f1, h3f2]
  have hinv := congrArg Subtype.val (inv_mul_cancel h)
  have hentry := congrFun (congrFun hinv (Sum.inl 0)) (Sum.inl 0)
  change
    (∑ k : SymplecticIndex,
      (h⁻¹).1 (Sum.inl 0) k * h.1 k (Sum.inl 0)) = 1 at hentry
  have hcol (i : SymplecticIndex) :
      h.1 i (Sum.inl 0) =
        (Pi.single (Sum.inl 0) d3 : IntegralLattice) i := by
    simpa [symplecticFirstColumn] using congrFun hfirst_d3 i
  have hd3mul :
      (h⁻¹).1 (Sum.inl 0) (Sum.inl 0) * d3 = 1 := by
    simpa [hcol, Pi.single, Fin.sum_univ_two] using hentry
  have hd3 : d3 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd3mul with hpos | hneg
    · exact hpos.2
    · have hd3nonneg : 0 ≤ d3 := by
        exact Int.natCast_nonneg (Int.gcd d1 d2)
      omega
  refine ⟨p, ?_, ?_⟩
  · exact elementarySymplecticSubgroup.mul_mem
      (elementarySymplecticSubgroup.mul_mem
        (symplecticDiagonalEmbedding_mem A3)
        (symplecticPlaneEmbedding_mem 1 A2))
      (symplecticPlaneEmbedding_mem 0 A1)
  · simpa [h, hd3] using hfirst_d3

theorem mem_elementarySymplecticSubgroup_of_firstColumn_eq_basis
    (h : IntegralSymplecticGroup)
    (hfirst : symplecticFirstColumn h = Pi.single (Sum.inl 0) 1) :
    h ∈ elementarySymplecticSubgroup := by
  have hcol (i : SymplecticIndex) :
      h.1 i (Sum.inl 0) =
        (Pi.single (Sum.inl 0) 1 : IntegralLattice) i := by
    simpa [symplecticFirstColumn] using congrFun hfirst i
  have he1e1 : h.1 (Sum.inl 0) (Sum.inl 0) = 1 := by
    simpa [Pi.single] using hcol (Sum.inl 0)
  have he2e1 : h.1 (Sum.inl 1) (Sum.inl 0) = 0 := by
    simpa [Pi.single] using hcol (Sum.inl 1)
  have hf1e1 : h.1 (Sum.inr 0) (Sum.inl 0) = 0 := by
    simpa [Pi.single] using hcol (Sum.inr 0)
  have hf2e1 : h.1 (Sum.inr 1) (Sum.inl 0) = 0 := by
    simpa [Pi.single] using hcol (Sum.inr 1)
  have hsym := (SymplecticGroup.mem_iff').mp h.2
  have hf1e2 :
      h.1 (Sum.inr 0) (Sum.inl 1) = 0 := by
    have e := congrFun (congrFun hsym (Sum.inl 0)) (Sum.inl 1)
    norm_num [Matrix.mul_apply, Matrix.J, Matrix.fromBlocks,
      he1e1, he2e1, hf1e1, hf2e1] at e
    omega
  have hf1f1 :
      h.1 (Sum.inr 0) (Sum.inr 0) = 1 := by
    have e := congrFun (congrFun hsym (Sum.inl 0)) (Sum.inr 0)
    norm_num [Matrix.mul_apply, Matrix.J, Matrix.fromBlocks,
      he1e1, he2e1, hf1e1, hf2e1] at e
    omega
  have hf1f2 :
      h.1 (Sum.inr 0) (Sum.inr 1) = 0 := by
    have e := congrFun (congrFun hsym (Sum.inl 0)) (Sum.inr 1)
    norm_num [Matrix.mul_apply, Matrix.J, Matrix.fromBlocks,
      he1e1, he2e1, hf1e1, hf2e1] at e
    omega
  let B : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![h.1 (Sum.inl 1) (Sum.inl 1),
        h.1 (Sum.inl 1) (Sum.inr 1);
        h.1 (Sum.inr 1) (Sum.inl 1),
        h.1 (Sum.inr 1) (Sum.inr 1)], by
      rw [Matrix.det_fin_two]
      norm_num
      have e := congrFun (congrFun hsym (Sum.inl 1)) (Sum.inr 1)
      norm_num [Matrix.mul_apply, Matrix.J, Matrix.fromBlocks,
        hf1e2, hf1f2] at e
      nlinarith⟩
  let p := symplecticPlaneEmbedding 1 B
  let m := p⁻¹ * h
  have hmdef : m = symplecticPlaneEmbedding 1 B⁻¹ * h := by
    simp [m, p]
  have hBdet := B.2
  rw [Matrix.det_fin_two] at hBdet
  norm_num [B] at hBdet
  have me1e1 : m.1 (Sum.inl 0) (Sum.inl 0) = 1 := by
    simp [hmdef, Matrix.mul_apply, symplecticPlaneEmbedding,
      symplecticPlaneMatrix, he1e1]
  have me2e1 : m.1 (Sum.inl 1) (Sum.inl 0) = 0 := by
    simp [hmdef, Matrix.mul_apply, symplecticPlaneEmbedding,
      symplecticPlaneMatrix, SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, he2e1, hf2e1]
  have mf1e1 : m.1 (Sum.inr 0) (Sum.inl 0) = 0 := by
    simp [hmdef, Matrix.mul_apply, symplecticPlaneEmbedding,
      symplecticPlaneMatrix, hf1e1]
  have mf2e1 : m.1 (Sum.inr 1) (Sum.inl 0) = 0 := by
    simp [hmdef, Matrix.mul_apply, symplecticPlaneEmbedding,
      symplecticPlaneMatrix, SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, he2e1, hf2e1]
  have mf1e2 : m.1 (Sum.inr 0) (Sum.inl 1) = 0 := by
    simp [hmdef, Matrix.mul_apply, symplecticPlaneEmbedding,
      symplecticPlaneMatrix, hf1e2]
  have mf1f1 : m.1 (Sum.inr 0) (Sum.inr 0) = 1 := by
    simp [hmdef, Matrix.mul_apply, symplecticPlaneEmbedding,
      symplecticPlaneMatrix, hf1f1]
  have mf1f2 : m.1 (Sum.inr 0) (Sum.inr 1) = 0 := by
    simp [hmdef, Matrix.mul_apply, symplecticPlaneEmbedding,
      symplecticPlaneMatrix, hf1f2]
  have me2e2 : m.1 (Sum.inl 1) (Sum.inl 1) = 1 := by
    simp [hmdef, B, Matrix.mul_apply, symplecticPlaneEmbedding,
      symplecticPlaneMatrix, SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two] ;
    nlinarith [hBdet]
  have me2f2 : m.1 (Sum.inl 1) (Sum.inr 1) = 0 := by
    simp [hmdef, B, Matrix.mul_apply, symplecticPlaneEmbedding,
      symplecticPlaneMatrix, SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two] ;
    ring
  have mf2e2 : m.1 (Sum.inr 1) (Sum.inl 1) = 0 := by
    simp [hmdef, B, Matrix.mul_apply, symplecticPlaneEmbedding,
      symplecticPlaneMatrix, SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two] ;
    ring
  have mf2f2 : m.1 (Sum.inr 1) (Sum.inr 1) = 1 := by
    simp [hmdef, B, Matrix.mul_apply, symplecticPlaneEmbedding,
      symplecticPlaneMatrix, SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two] ;
    nlinarith [hBdet]
  let a := m.1 (Sum.inl 0) (Sum.inl 1)
  let b := m.1 (Sum.inl 0) (Sum.inr 0)
  let c := m.1 (Sum.inl 0) (Sum.inr 1)
  let q := m.1 (Sum.inl 1) (Sum.inr 0)
  let t := m.1 (Sum.inr 1) (Sum.inr 0)
  have msym := (SymplecticGroup.mem_iff').mp m.2
  have hta : t = -a := by
    have e := congrFun (congrFun msym (Sum.inl 1)) (Sum.inr 0)
    norm_num [Matrix.mul_apply, Matrix.J, Matrix.fromBlocks,
      me1e1, me2e1, mf1e1, mf2e1, mf1e2, mf1f1, mf1f2,
      me2e2, me2f2, mf2e2, mf2f2, a, t] at e
    omega
  have hcq : c = q := by
    have e := congrFun (congrFun msym (Sum.inr 0)) (Sum.inr 1)
    norm_num [Matrix.mul_apply, Matrix.J, Matrix.fromBlocks,
      me1e1, me2e1, mf1e1, mf2e1, mf1e2, mf1f1, mf1f2,
      me2e2, me2f2, mf2e2, mf2f2, c, q] at e
    omega
  let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![1, a; 0, 1], by norm_num [Matrix.det_fin_two]⟩
  let S : Matrix (Fin 2) (Fin 2) ℤ :=
    !![b - a * q, q; q, 0]
  have hS : S.transpose = S := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S, Matrix.transpose_apply]
  have hm_factor :
      m = symplecticDiagonalEmbedding A * upperShear S hS := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [symplecticDiagonalEmbedding, symplecticDiagonalMatrix,
        sl2InverseTransposeMatrix, upperShear, Matrix.fromBlocks,
        Matrix.mul_apply, A, S, a, b, c, q, t,
        me1e1, me2e1, mf1e1, mf2e1, mf1e2, mf1f1, mf1f2,
        me2e2, me2f2, mf2e2, mf2f2, hta, hcq]
  have hm_mem : m ∈ elementarySymplecticSubgroup := by
    rw [hm_factor]
    exact elementarySymplecticSubgroup.mul_mem
      (symplecticDiagonalEmbedding_mem A)
      (upperShear_mem S hS)
  have hp_mem : p ∈ elementarySymplecticSubgroup :=
    symplecticPlaneEmbedding_mem 1 B
  have hpm : p * m = h := by
    simp [m]
  rw [← hpm]
  exact elementarySymplecticSubgroup.mul_mem hp_mem hm_mem

theorem elementarySymplecticSubgroup_eq_top :
    elementarySymplecticSubgroup = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨p, hp, hfirst⟩ :=
    exists_elementary_mul_firstColumn_eq_basis g
  have hpg :
      p * g ∈ elementarySymplecticSubgroup :=
    mem_elementarySymplecticSubgroup_of_firstColumn_eq_basis
      (p * g) hfirst
  have hg : g = p⁻¹ * (p * g) := by simp
  rw [hg]
  exact elementarySymplecticSubgroup.mul_mem
    (elementarySymplecticSubgroup.inv_mem hp) hpg

theorem elementarySymplecticGenerators_generate :
    Subgroup.closure (elementarySymplecticGenerators :
      Set IntegralSymplecticGroup) = ⊤ :=
  elementarySymplecticSubgroup_eq_top

def gammaZeroQuotientLift
    (g : IntegralSymplecticGroup) : constructedGammaZeroGroup :=
  ⟨0, g⟩

def gammaZeroBasisTranslation
    (i : SymplecticIndex) : constructedGammaZeroGroup :=
  ⟨Pi.single i 1, 1⟩

noncomputable def gammaZeroElementaryGenerators :
    Finset constructedGammaZeroGroup := by
  classical
  let positive : Finset constructedGammaZeroGroup :=
    positiveElementarySymplecticGeneratorList.toFinset.image
        gammaZeroQuotientLift ∪
      (Finset.univ : Finset SymplecticIndex).image gammaZeroBasisTranslation
  exact positive ∪ positive.image Inv.inv

def gammaZeroQuotientLiftHom :
    IntegralSymplecticGroup →* constructedGammaZeroGroup where
  toFun g := ⟨0, g⟩
  map_one' := rfl
  map_mul' g h := by
    apply CocycleExtension.ext
    · change 0 = 0 + g • (0 : IntegralLattice) + 0
      have hz : g • (0 : IntegralLattice) = 0 := by
        change g.1.mulVec (0 : IntegralLattice) = 0
        exact Matrix.mulVec_zero g.1
      rw [hz]
      simp
    · rfl

@[simp]
theorem gammaZeroQuotientLiftHom_apply
    (g : IntegralSymplecticGroup) :
    gammaZeroQuotientLiftHom g = gammaZeroQuotientLift g :=
  rfl

noncomputable def gammaZeroElementarySubgroup :
    Subgroup constructedGammaZeroGroup :=
  Subgroup.closure (gammaZeroElementaryGenerators :
    Set constructedGammaZeroGroup)

private theorem gammaZero_positive_quotient_mem
    {g : IntegralSymplecticGroup}
    (hg : g ∈ positiveElementarySymplecticGeneratorList) :
    gammaZeroQuotientLift g ∈ gammaZeroElementarySubgroup := by
  classical
  apply Subgroup.subset_closure
  change gammaZeroQuotientLift g ∈
    (positiveElementarySymplecticGeneratorList.toFinset.image
          gammaZeroQuotientLift ∪
        (Finset.univ : Finset SymplecticIndex).image
          gammaZeroBasisTranslation) ∪
      (positiveElementarySymplecticGeneratorList.toFinset.image
          gammaZeroQuotientLift ∪
        (Finset.univ : Finset SymplecticIndex).image
          gammaZeroBasisTranslation).image Inv.inv
  exact Finset.mem_union_left _
    (Finset.mem_union_left _
      (Finset.mem_image.mpr
        ⟨g, List.mem_toFinset.mpr hg, rfl⟩))

private theorem gammaZero_basisTranslation_mem
    (i : SymplecticIndex) :
    gammaZeroBasisTranslation i ∈ gammaZeroElementarySubgroup := by
  apply Subgroup.subset_closure
  simp [gammaZeroElementaryGenerators]

private theorem gammaZero_quotientLift_mem
    (g : IntegralSymplecticGroup) :
    gammaZeroQuotientLift g ∈ gammaZeroElementarySubgroup := by
  classical
  let Q := gammaZeroElementarySubgroup.comap gammaZeroQuotientLiftHom
  have hgens :
      (elementarySymplecticGenerators :
        Set IntegralSymplecticGroup) ⊆ Q := by
    intro x hx
    change gammaZeroQuotientLiftHom x ∈ gammaZeroElementarySubgroup
    rw [gammaZeroQuotientLiftHom_apply]
    change x ∈
      positiveElementarySymplecticGeneratorList.toFinset ∪
        positiveElementarySymplecticGeneratorList.toFinset.image Inv.inv at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact gammaZero_positive_quotient_mem
        (List.mem_toFinset.mp hx)
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      change gammaZeroQuotientLiftHom y⁻¹ ∈ gammaZeroElementarySubgroup
      rw [map_inv]
      exact gammaZeroElementarySubgroup.inv_mem
        (gammaZero_positive_quotient_mem (List.mem_toFinset.mp hy))
  have hle : elementarySymplecticSubgroup ≤ Q :=
    (Subgroup.closure_le Q).2 hgens
  change g ∈ Q
  exact hle (by
    rw [elementarySymplecticSubgroup_eq_top]
    exact Subgroup.mem_top g)

private theorem gammaZero_translation_mem
    (v : IntegralLattice) :
    ({ fst := v, snd := (1 : IntegralSymplecticGroup) } :
      constructedGammaZeroGroup) ∈ gammaZeroElementarySubgroup := by
  let V : AddSubgroup IntegralLattice :=
    { carrier := {v |
        ({ fst := v, snd := (1 : IntegralSymplecticGroup) } :
          constructedGammaZeroGroup) ∈ gammaZeroElementarySubgroup}
      zero_mem' := by
        change (1 : constructedGammaZeroGroup) ∈ gammaZeroElementarySubgroup
        exact gammaZeroElementarySubgroup.one_mem
      add_mem' := by
        intro v w hv hw
        have hmul := gammaZeroElementarySubgroup.mul_mem hv hw
        change
          ({ fst := v + w, snd := (1 : IntegralSymplecticGroup) } :
            constructedGammaZeroGroup) ∈ gammaZeroElementarySubgroup
        have heq :
            ({ fst := v + w, snd := (1 : IntegralSymplecticGroup) } :
              constructedGammaZeroGroup) =
              ({ fst := v, snd := (1 : IntegralSymplecticGroup) } :
                constructedGammaZeroGroup) *
              ({ fst := w, snd := (1 : IntegralSymplecticGroup) } :
                constructedGammaZeroGroup) := by
          apply CocycleExtension.ext
          · change v + w = v + (1 : IntegralSymplecticGroup) • w + 0
            rw [one_smul]
            simp
          · rw [CocycleExtension.mul_snd]
            simp
        rw [heq]
        exact hmul
      neg_mem' := by
        intro v hv
        have hinv := gammaZeroElementarySubgroup.inv_mem hv
        change
          ({ fst := -v, snd := (1 : IntegralSymplecticGroup) } :
            constructedGammaZeroGroup) ∈ gammaZeroElementarySubgroup
        have heq :
            ({ fst := -v, snd := (1 : IntegralSymplecticGroup) } :
              constructedGammaZeroGroup) =
              (({ fst := v, snd := (1 : IntegralSymplecticGroup) } :
                constructedGammaZeroGroup)⁻¹) := by
          apply CocycleExtension.ext
          · funext i
            simp only [Pi.neg_apply, CocycleExtension.inv_fst, inv_one,
              NormalizedAddCocycle.zero_apply, add_zero, neg_inj]
            exact congr_fun
              (one_smul IntegralSymplecticGroup v).symm i
          · rw [CocycleExtension.inv_snd]
            simp
        rw [heq]
        exact hinv }
  have hbasis (i : SymplecticIndex) :
      Pi.single i 1 ∈ V := by
    change gammaZeroBasisTranslation i ∈ gammaZeroElementarySubgroup
    exact gammaZero_basisTranslation_mem i
  have hvsum :
      v = ∑ i : SymplecticIndex, v i • Pi.single i 1 := by
    funext j
    simp [Pi.single_apply]
  rw [hvsum]
  exact V.sum_mem fun i _ => V.zsmul_mem (hbasis i) (v i)

theorem gammaZeroElementaryGenerators_generate :
    IsGeneratingSet constructedGammaZeroGroup
      gammaZeroElementaryGenerators := by
  change gammaZeroElementarySubgroup = ⊤
  rw [eq_top_iff]
  intro x _
  have ht := gammaZero_translation_mem x.fst
  have hq := gammaZero_quotientLift_mem x.snd
  have hmul := gammaZeroElementarySubgroup.mul_mem ht hq
  have hx :
      ({ fst := x.fst, snd := (1 : IntegralSymplecticGroup) } :
          constructedGammaZeroGroup) *
        ({ fst := 0, snd := x.snd } :
          constructedGammaZeroGroup) = x := by
    apply CocycleExtension.ext
    · simp
    · simp
  exact hx ▸ hmul

end ConnesRigidity
