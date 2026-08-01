
import ConnesRigidity.PropertyTExactCertificateOrbitPositivity

namespace ConnesRigidity.OrbitPositivity

open scoped BigOperators

universe u v

variable {ι : Type u} [Fintype ι] [LinearOrder ι]
variable {κ : Type v} [Fintype κ] [LinearOrder κ]

noncomputable def congruenceAtom
    {G : Type*} [Group G]
    (atom : ι → RationalGroupRing G)
    (change : Matrix ι κ ℚ) (column : κ) : RationalGroupRing G :=
  ∑ row, change row column • atom row

omit [LinearOrder ι] [LinearOrder κ] in

theorem matrixAtomExpansion_congruence
    {G : Type*} [Group G]
    (atom : ι → RationalGroupRing G)
    (change : Matrix ι κ ℚ)
    (matrix : Matrix κ κ ℚ) :
    matrixAtomExpansion atom (change * matrix * change.transpose) =
      matrixAtomExpansion (congruenceAtom atom change) matrix := by
  classical
  have hatom (first second : κ) :
      RationalGroupRing.adjoint (congruenceAtom atom change first) *
          congruenceAtom atom change second =
        ∑ i : ι, ∑ j : ι,
          (change i first * change j second) •
            (RationalGroupRing.adjoint (atom i) * atom j) := by
    unfold congruenceAtom
    rw [RationalGroupRing.adjoint_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [RationalGroupRing.adjoint_smul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  unfold matrixAtomExpansion
  simp_rw [hatom, Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.sum_smul]
  simp_rw [Finset.smul_sum, smul_smul]
  have hswap
      (f : ι → ι → κ → κ → RationalGroupRing G) :
      (∑ i, ∑ j, ∑ second, ∑ first, f i j second first) =
        ∑ first, ∑ second, ∑ i, ∑ j, f i j second first := by
    calc
      (∑ i, ∑ j, ∑ second, ∑ first, f i j second first) =
          ∑ i, ∑ j, ∑ first, ∑ second, f i j second first := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_comm
      _ = ∑ i, ∑ first, ∑ j, ∑ second, f i j second first := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ first, ∑ i, ∑ j, ∑ second, f i j second first :=
        Finset.sum_comm
      _ = ∑ first, ∑ i, ∑ second, ∑ j, f i j second first := by
        apply Finset.sum_congr rfl
        intro first _
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ first, ∑ second, ∑ i, ∑ j, f i j second first := by
        apply Finset.sum_congr rfl
        intro first _
        exact Finset.sum_comm
  calc
    (∑ i : ι, ∑ j : ι, ∑ second : κ, ∑ first : κ,
      (change i first * matrix first second * change j second) •
        (RationalGroupRing.adjoint (atom i) * atom j)) =
        ∑ first : κ, ∑ second : κ, ∑ i : ι, ∑ j : ι,
          (change i first * matrix first second * change j second) •
            (RationalGroupRing.adjoint (atom i) * atom j) :=
      hswap (fun (i j : ι) (second first : κ) =>
        (change i first * matrix first second * change j second) •
          (RationalGroupRing.adjoint (atom i) * atom j))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring

theorem matrix_eq_inverse_congruence
    (matrix : Matrix ι ι ℚ)
    (change inverse : Matrix ι ι ℚ)
    (hinverse : change * inverse = 1) :
    matrix = inverse.transpose *
      (change.transpose * matrix * change) * inverse := by
  calc
    matrix = 1 * matrix * 1 := by simp
    _ = (change * inverse).transpose * matrix *
        (change * inverse) := by rw [hinverse, Matrix.transpose_one]
    _ = inverse.transpose *
      (change.transpose * matrix * change) * inverse := by
        rw [Matrix.transpose_mul]
        simp [Matrix.mul_assoc]

omit [LinearOrder ι] [LinearOrder κ] in

theorem matrixAtomExpansion_congruence_isPositiveSumOfSquares
    {G : Type*} [Group G]
    (atom : ι → RationalGroupRing G)
    (change : Matrix ι κ ℚ)
    (matrix : Matrix κ κ ℚ)
    (hpositive : RationalGroupRing.IsPositiveSumOfSquares
      (matrixAtomExpansion (congruenceAtom atom change) matrix)) :
    RationalGroupRing.IsPositiveSumOfSquares
      (matrixAtomExpansion atom (change * matrix * change.transpose)) := by
  rw [matrixAtomExpansion_congruence]
  exact hpositive

theorem matrixAtomExpansion_isPositiveSumOfSquares_of_congruence
    {G : Type*} [Group G]
    (atom : ι → RationalGroupRing G)
    (matrix change inverse : Matrix ι ι ℚ)
    (hinverse : change * inverse = 1)
    (hpositive : RationalGroupRing.IsPositiveSumOfSquares
      (matrixAtomExpansion (congruenceAtom atom inverse.transpose)
        (change.transpose * matrix * change))) :
    RationalGroupRing.IsPositiveSumOfSquares
      (matrixAtomExpansion atom matrix) := by
  rw [matrix_eq_inverse_congruence matrix change inverse hinverse]
  have hcongruence := matrixAtomExpansion_congruence
    atom inverse.transpose (change.transpose * matrix * change)
  simpa using hcongruence ▸ hpositive

end ConnesRigidity.OrbitPositivity
