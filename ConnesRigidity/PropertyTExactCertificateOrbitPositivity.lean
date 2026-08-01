
import ConnesRigidity.PropertyTExactCertificateSDD
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace ConnesRigidity

namespace OrbitPositivity

open scoped BigOperators

universe u v

variable {ι : Type u} [Fintype ι] [LinearOrder ι]
variable {ρ : Type v} [Fintype ρ]

noncomputable def matrixAtomExpansion
    {G : Type*} [Group G]
    (atom : ι → RationalGroupRing G)
    (matrix : Matrix ι ι ℚ) : RationalGroupRing G :=
  ∑ i, ∑ j, matrix i j •
    (RationalGroupRing.adjoint (atom i) * atom j)

theorem positiveSumOfSquares_add
    {G : Type*} [Group G]
    {left right : RationalGroupRing G}
    (hleft : RationalGroupRing.IsPositiveSumOfSquares left)
    (hright : RationalGroupRing.IsPositiveSumOfSquares right) :
    RationalGroupRing.IsPositiveSumOfSquares (left + right) := by
  obtain ⟨xs, hx, hleft⟩ := hleft
  obtain ⟨ys, hy, hright⟩ := hright
  refine ⟨xs ++ ys, ?_, ?_⟩
  · intro square hsquare
    rcases List.mem_append.mp hsquare with hsquare | hsquare
    · exact hx square hsquare
    · exact hy square hsquare
  · rw [List.map_append, List.sum_append, ← hleft, ← hright]

theorem positiveSumOfSquares_smul
    {G : Type*} [Group G]
    {value : RationalGroupRing G}
    (hvalue : RationalGroupRing.IsPositiveSumOfSquares value)
    {scale : ℚ} (hscale : 0 ≤ scale) :
    RationalGroupRing.IsPositiveSumOfSquares (scale • value) := by
  obtain ⟨xs, hx, hvalue⟩ := hvalue
  refine ⟨xs.map (fun square ↦ (scale * square.1, square.2)), ?_, ?_⟩
  · intro square hsquare
    obtain ⟨original, horiginal, heq⟩ := List.mem_map.mp hsquare
    rw [← heq]
    exact mul_nonneg hscale (hx original horiginal)
  · rw [hvalue]
    clear hx hvalue
    induction xs with
    | nil => simp
    | cons square xs ih => simp [smul_add, smul_smul, ih]

omit [LinearOrder ι] in

theorem matrixAtomExpansion_add
    {G : Type*} [Group G]
    (atom : ι → RationalGroupRing G)
    (left right : Matrix ι ι ℚ) :
    matrixAtomExpansion atom (left + right) =
      matrixAtomExpansion atom left + matrixAtomExpansion atom right := by
  classical
  unfold matrixAtomExpansion
  simp_rw [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

omit [LinearOrder ι] in

theorem atomVector_square_eq_expansion
    {G : Type*} [Group G]
    (atom : ι → RationalGroupRing G)
    (coefficient : ι → ℚ) :
    RationalGroupRing.adjoint
        (SDDCertificate.atomVector atom coefficient) *
      SDDCertificate.atomVector atom coefficient =
        ∑ i, ∑ j, (coefficient i * coefficient j) •
          (RationalGroupRing.adjoint (atom i) * atom j) := by
  classical
  unfold SDDCertificate.atomVector
  rw [RationalGroupRing.adjoint_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [RationalGroupRing.adjoint_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

omit [LinearOrder ι] in

theorem transpose_mul_matrixAtomExpansion
    {G : Type*} [Group G]
    (atom : ι → RationalGroupRing G)
    (factor : Matrix ρ ι ℚ) :
    matrixAtomExpansion atom (factor.transpose * factor) =
      ∑ row : ρ,
        RationalGroupRing.adjoint
            (SDDCertificate.atomVector atom (factor row)) *
          SDDCertificate.atomVector atom (factor row) := by
  classical
  simp_rw [atomVector_square_eq_expansion]
  unfold matrixAtomExpansion
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_smul]
  calc
    (∑ i, ∑ j, ∑ row : ρ,
      (factor row i * factor row j) •
        (RationalGroupRing.adjoint (atom i) * atom j)) =
        ∑ i, ∑ row : ρ, ∑ j,
          (factor row i * factor row j) •
            (RationalGroupRing.adjoint (atom i) * atom j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ row : ρ, ∑ i, ∑ j,
          (factor row i * factor row j) •
            (RationalGroupRing.adjoint (atom i) * atom j) := by
      rw [Finset.sum_comm]

omit [LinearOrder ι] in

theorem transpose_mul_expansion_isPositiveSumOfSquares
    {G : Type*} [Group G]
    (atom : ι → RationalGroupRing G)
    (factor : Matrix ρ ι ℚ) :
    RationalGroupRing.IsPositiveSumOfSquares
      (matrixAtomExpansion atom (factor.transpose * factor)) := by
  classical
  apply RationalGroupRing.IsSumOfSquares.isPositiveSumOfSquares
  refine ⟨Finset.univ.toList.map
    (fun row : ρ ↦ SDDCertificate.atomVector atom (factor row)), ?_⟩
  rw [transpose_mul_matrixAtomExpansion atom factor]
  simp [List.map_map, Function.comp_def]

theorem gram_add_sdd_expansion_isPositiveSumOfSquares
    {G : Type*} [Group G]
    (atom : ι → RationalGroupRing G)
    (factor : Matrix ρ ι ℚ)
    (residual : Matrix ι ι ℚ)
    (hsymm : residual.IsSymm)
    (hdominant : SDDCertificate.IsDiagonallyDominant residual) :
    RationalGroupRing.IsPositiveSumOfSquares
      (matrixAtomExpansion atom
        (factor.transpose * factor + residual)) := by
  rw [matrixAtomExpansion_add]
  exact positiveSumOfSquares_add
    (transpose_mul_expansion_isPositiveSumOfSquares atom factor)
    (SDDCertificate.matrixAtomExpansion_isPositiveSumOfSquares
      atom residual hsymm hdominant)

theorem scaled_gram_add_sdd_expansion_isPositiveSumOfSquares
    {G : Type*} [Group G]
    (atom : ι → RationalGroupRing G)
    (matrix : Matrix ι ι ℚ)
    (factor : Matrix ρ ι ℚ)
    (residual : Matrix ι ι ℚ)
    (scale : ℚ) (hscale : 0 < scale)
    (hidentity : scale ^ 2 • matrix =
      factor.transpose * factor + residual)
    (hsymm : residual.IsSymm)
    (hdominant : SDDCertificate.IsDiagonallyDominant residual) :
    RationalGroupRing.IsPositiveSumOfSquares
      (matrixAtomExpansion atom matrix) := by
  have hpositive := gram_add_sdd_expansion_isPositiveSumOfSquares
    atom factor residual hsymm hdominant
  rw [← hidentity] at hpositive
  have hexpansion :
      matrixAtomExpansion atom (scale ^ 2 • matrix) =
        scale ^ 2 • matrixAtomExpansion atom matrix := by
    unfold matrixAtomExpansion
    simp_rw [Matrix.smul_apply, smul_eq_mul, mul_smul]
    simp_rw [Finset.smul_sum]
  rw [hexpansion] at hpositive
  have hscale2 : 0 < scale ^ 2 := sq_pos_of_pos hscale
  convert positiveSumOfSquares_smul hpositive (inv_nonneg.mpr hscale2.le) using 1
  simp [hscale2.ne']

end OrbitPositivity

end ConnesRigidity
