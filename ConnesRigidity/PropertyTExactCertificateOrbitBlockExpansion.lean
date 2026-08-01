


import ConnesRigidity.PropertyTExactCertificateOrbitAlgebra
import ConnesRigidity.PropertyTExactCertificateOrbitBlockCertificate
import ConnesRigidity.PropertyTExactCertificateOrbitGramBoundaryValidation
import ConnesRigidity.PropertyTExactCertificateOrbitMatrixAlgebra
import ConnesRigidity.PropertyTExactCertificateOrbitRadixMatrixSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitRadixVerifiedIdentity
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumSoundness











namespace ConnesRigidity

open scoped BigOperators

universe u v w

namespace OrbitPositivity

variable {ι : Type u} [Fintype ι] [LinearOrder ι]

omit [LinearOrder ι] in


theorem matrixAtomExpansion_finset_sum
    {G : Type*} [Group G] {β : Type*}
    (atom : ι → RationalGroupRing G)
    (indices : Finset β) (matrix : β → Matrix ι ι ℚ) :
    matrixAtomExpansion atom (∑ index ∈ indices, matrix index) =
      ∑ index ∈ indices, matrixAtomExpansion atom (matrix index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [matrixAtomExpansion]
  | @insert index indices hindex ih =>
      simp [hindex, matrixAtomExpansion_add, ih]

omit [LinearOrder ι] in


theorem matrixAtomExpansion_smul
    {G : Type*} [Group G]
    (atom : ι → RationalGroupRing G)
    (scale : ℚ) (matrix : Matrix ι ι ℚ) :
    matrixAtomExpansion atom (scale • matrix) =
      scale • matrixAtomExpansion atom matrix := by
  classical
  unfold matrixAtomExpansion
  simp_rw [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

omit [LinearOrder ι] in



theorem sum_matrixAtomExpansion_congruence
    {G : Type*} [Group G]
    {β : Type v} [Fintype β]
    {δ : β → Type w}
    [∀ index, Fintype (δ index)]
    [∀ index, LinearOrder (δ index)]
    (atom : ι → RationalGroupRing G)
    (weight : ∀ index, Matrix ι (δ index) ℚ)
    (block : ∀ index, Matrix (δ index) (δ index) ℚ) :
    (∑ index,
      matrixAtomExpansion (congruenceAtom atom (weight index))
        (block index)) =
      matrixAtomExpansion atom
        (∑ index, weight index * block index *
          (weight index).transpose) := by
  classical
  rw [matrixAtomExpansion_finset_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact (matrixAtomExpansion_congruence atom
    (weight index) (block index)).symm

end OrbitPositivity

namespace AffineSymplecticOrbitCertificate

variable {G : Type u} [Group G]





theorem orbitBlockGram_isSymm (block : Fin 28) :
    (blockGram block.val).IsSymm := by
  have hfactor := blockFactorIdentity_of_checks block.val
    (orbitBlockFactorIdentityChecks block)
  have hresidual := blockResidualSymmetric_of_checks block.val
    (orbitBlockResidualSymmetryChecks block)
  norm_num [factorScale] at hfactor
  rw [hfactor]
  exact (Matrix.isSymm_transpose_mul_self (blockFactor block.val)).add
    hresidual



theorem orbitWeightedBlockGram_isSymm (block : Fin 28) :
    (orbitBlockWeight block * blockGram block.val *
      (orbitBlockWeight block).transpose).IsSymm := by
  change
    (orbitBlockWeight block * blockGram block.val *
      (orbitBlockWeight block).transpose).transpose = _
  simp [Matrix.transpose_mul, (orbitBlockGram_isSymm block).eq,
    Matrix.mul_assoc]



theorem orbitWeightedBlockGram_sum_isSymm :
    (∑ block : Fin 28,
      orbitBlockWeight block * blockGram block.val *
        (orbitBlockWeight block).transpose).IsSymm := by
  change
    (∑ block : Fin 28,
      orbitBlockWeight block * blockGram block.val *
        (orbitBlockWeight block).transpose).transpose = _
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro block _
  exact (orbitWeightedBlockGram_isSymm block).eq




theorem gramEntry_swap_of_radix_identity
    (integerIdentity : ∀ row column : Fin 424,
      orbitRadixComputedEntry row column =
        congruenceInverseScale ^ 2 *
          gramEntry (row.val + 1) (column.val + 1)) :
    ∀ i j : Fin 425, gramEntry i.val j.val = gramEntry j.val i.val := by
  have hreduced (row column : Fin 424) :
      gramEntry (row.val + 1) (column.val + 1) =
        gramEntry (column.val + 1) (row.val + 1) := by
    have hsymm := orbitWeightedBlockGram_sum_isSymm.apply column row
    rw [orbitBlockWeight_sum_gram_apply,
      orbitBlockWeight_sum_gram_apply] at hsymm
    have hcomputed :
        orbitRadixComputedEntry row column =
          orbitRadixComputedEntry column row := by
      exact_mod_cast hsymm
    rw [integerIdentity, integerIdentity] at hcomputed
    norm_num [congruenceInverseScale] at hcomputed
    omega
  intro i j
  refine Fin.cases ?_ ?_ i
  · exact gramEntry_zero_swap j
  · intro i
    refine Fin.cases ?_ ?_ j
    · exact (gramEntry_zero_swap i.succ).symm
    · intro j
      exact hreduced i j





theorem scaledBlockExpansion_eq_fullGramExpansion_of_zero_sums
    {n : ℕ} {β : Type v} [Fintype β]
    {δ : β → Type w}
    [∀ index, Fintype (δ index)]
    [∀ index, LinearOrder (δ index)]
    (basis : Fin (n + 1) → G)
    (gram : Fin (n + 1) → Fin (n + 1) → ℚ)
    (scale : ℚ) (hscale : scale ≠ 0)
    (weight : ∀ index, Matrix (Fin n) (δ index) ℚ)
    (block : ∀ index, Matrix (δ index) (δ index) ℚ)
    (hrow : ∀ i, ∑ j, gram i j = 0)
    (hcol : ∀ j, ∑ i, gram i j = 0)
    (hentry : ∀ i j : Fin n,
      (∑ index,
        (weight index * block index * (weight index).transpose) i j) =
        scale ^ 2 * gram i.succ j.succ) :
    (scale ^ 2)⁻¹ •
      (∑ index,
        OrbitPositivity.matrixAtomExpansion
          (OrbitPositivity.congruenceAtom
            (reducedGroupAtom basis) (weight index))
          (block index)) =
      fullGramExpansion basis gram := by
  classical
  rw [fullGramExpansion_eq_reduced_of_zero_sums basis gram hrow hcol]
  let reducedGram : Matrix (Fin n) (Fin n) ℚ :=
    fun i j => gram i.succ j.succ
  change
    (scale ^ 2)⁻¹ •
      (∑ index,
        OrbitPositivity.matrixAtomExpansion
          (OrbitPositivity.congruenceAtom
            (reducedGroupAtom basis) (weight index))
          (block index)) =
      OrbitPositivity.matrixAtomExpansion
        (reducedGroupAtom basis) reducedGram
  rw [OrbitPositivity.sum_matrixAtomExpansion_congruence]
  have hmatrix :
      (∑ index, weight index * block index *
        (weight index).transpose) =
        scale ^ 2 • reducedGram := by
    ext i j
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      reducedGram] using hentry i j
  rw [hmatrix, OrbitPositivity.matrixAtomExpansion_smul, smul_smul]
  simp [hscale]



theorem scaledBlockExpansion_eq_fullGramExpansion
    {n : ℕ} {β : Type v} [Fintype β]
    {δ : β → Type w}
    [∀ index, Fintype (δ index)]
    [∀ index, LinearOrder (δ index)]
    (basis : Fin (n + 1) → G)
    (gram : Fin (n + 1) → Fin (n + 1) → ℚ)
    (scale : ℚ) (hscale : scale ≠ 0)
    (weight : ∀ index, Matrix (Fin n) (δ index) ℚ)
    (block : ∀ index, Matrix (δ index) (δ index) ℚ)
    (hsymm : ∀ i j, gram i j = gram j i)
    (hrow : ∀ i, ∑ j, gram i j = 0)
    (hentry : ∀ i j : Fin n,
      (∑ index,
        (weight index * block index * (weight index).transpose) i j) =
        scale ^ 2 * gram i.succ j.succ) :
    (scale ^ 2)⁻¹ •
      (∑ index,
        OrbitPositivity.matrixAtomExpansion
          (OrbitPositivity.congruenceAtom
            (reducedGroupAtom basis) (weight index))
          (block index)) =
      fullGramExpansion basis gram := by
  apply scaledBlockExpansion_eq_fullGramExpansion_of_zero_sums
    basis gram scale hscale weight block hrow _ hentry
  intro j
  simpa only [hsymm] using hrow j




theorem orbitBlockCandidate_eq_fullGramExpansion_of_zero_sums
    (weight : ∀ block : Fin 28,
      Matrix (Fin 424) (Fin (blockDimension block.val)) ℚ)
    (hatom : ∀ (block : Fin 28)
      (column : Fin (blockDimension block.val)),
      orbitBlockAtom block column =
        OrbitPositivity.congruenceAtom
          (reducedGroupAtom orbitBasis) (weight block) column)
    (hrow : ∀ i : Fin 425,
      ∑ j : Fin 425, (gramEntry i.val j.val : ℚ) = 0)
    (hcol : ∀ j : Fin 425,
      ∑ i : Fin 425, (gramEntry i.val j.val : ℚ) = 0)
    (hentry : ∀ i j : Fin 424,
      (∑ block : Fin 28,
        (weight block * blockGram block.val *
          (weight block).transpose) i j) =
        ((congruenceInverseScale : Int) : ℚ) ^ 2 *
          (gramEntry (i.val + 1) (j.val + 1) : ℚ)) :
    orbitBlockCandidate =
      fullGramExpansion orbitBasis
        (fun i j : Fin 425 => (gramEntry i.val j.val : ℚ)) := by
  have hscale : (((congruenceInverseScale : Int) : ℚ)) ≠ 0 := by
    norm_num [congruenceInverseScale]
  have h := scaledBlockExpansion_eq_fullGramExpansion_of_zero_sums
    orbitBasis
    (fun i j : Fin 425 => (gramEntry i.val j.val : ℚ))
    (((congruenceInverseScale : Int) : ℚ)) hscale weight
    (fun block : Fin 28 => blockGram block.val)
    hrow hcol hentry
  have hatom_fun (block : Fin 28) :
      orbitBlockAtom block =
        OrbitPositivity.congruenceAtom
          (reducedGroupAtom orbitBasis) (weight block) := by
    funext column
    exact hatom block column
  rw [orbitBlockCandidate]
  simp_rw [hatom_fun]
  exact h





theorem orbitBlockCandidate_eq_fullGramExpansion_of_entries
    (weight : ∀ block : Fin 28,
      Matrix (Fin 424) (Fin (blockDimension block.val)) ℚ)
    (hatom : ∀ (block : Fin 28)
      (column : Fin (blockDimension block.val)),
      orbitBlockAtom block column =
        OrbitPositivity.congruenceAtom
          (reducedGroupAtom orbitBasis) (weight block) column)
    (hsymm : ∀ i j : Fin 425,
      gramEntry i.val j.val = gramEntry j.val i.val)
    (hrow : ∀ i : Fin 425,
      ∑ j : Fin 425, (gramEntry i.val j.val : ℚ) = 0)
    (hentry : ∀ i j : Fin 424,
      (∑ block : Fin 28,
        (weight block * blockGram block.val *
          (weight block).transpose) i j) =
        ((congruenceInverseScale : Int) : ℚ) ^ 2 *
          (gramEntry (i.val + 1) (j.val + 1) : ℚ)) :
    orbitBlockCandidate =
      fullGramExpansion orbitBasis
        (fun i j : Fin 425 => (gramEntry i.val j.val : ℚ)) := by
  apply orbitBlockCandidate_eq_fullGramExpansion_of_zero_sums
    weight hatom hrow _ hentry
  intro j
  calc
    (∑ i : Fin 425, (gramEntry i.val j.val : ℚ)) =
        ∑ i : Fin 425, (gramEntry j.val i.val : ℚ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact_mod_cast hsymm i j
    _ = 0 := hrow j






theorem orbitBlockCandidate_eq_fullGramExpansion_of_radix_identity
    (hsymm : ∀ i j : Fin 425,
      gramEntry i.val j.val = gramEntry j.val i.val)
    (hrow : ∀ i : Fin 425,
      ∑ j : Fin 425, (gramEntry i.val j.val : ℚ) = 0)
    (integerIdentity : ∀ row column : Fin 424,
      orbitRadixComputedEntry row column =
        congruenceInverseScale ^ 2 *
          gramEntry (row.val + 1) (column.val + 1)) :
    orbitBlockCandidate =
      fullGramExpansion orbitBasis
        (fun i j : Fin 425 => (gramEntry i.val j.val : ℚ)) := by
  apply orbitBlockCandidate_eq_fullGramExpansion_of_entries
    orbitBlockWeight
  · intro block column
    rfl
  · exact hsymm
  · exact hrow
  · intro row column
    simpa [congruenceInverseScale, Matrix.sum_apply] using
      orbitReducedGram_radix_identity_of_integer integerIdentity row column





theorem orbitBlockCandidate_eq_fullGramExpansion_of_integer_identity
    (integerIdentity : ∀ row column : Fin 424,
      orbitRadixComputedEntry row column =
        congruenceInverseScale ^ 2 *
          gramEntry (row.val + 1) (column.val + 1)) :
    orbitBlockCandidate =
      fullGramExpansion orbitBasis
        (fun i j : Fin 425 => (gramEntry i.val j.val : ℚ)) :=
  orbitBlockCandidate_eq_fullGramExpansion_of_radix_identity
    (gramEntry_swap_of_radix_identity integerIdentity)
    orbitGram_rowSum integerIdentity



theorem orbitGramEntry_swap (i j : Fin 425) :
    gramEntry i.val j.val = gramEntry j.val i.val :=
  gramEntry_swap_of_radix_identity orbitRadix_integer_identity i j





theorem orbitBlockCandidate_eq_fullGramExpansion :
    orbitBlockCandidate =
      fullGramExpansion orbitBasis
        (fun i j : Fin 425 => (gramEntry i.val j.val : ℚ)) :=
  orbitBlockCandidate_eq_fullGramExpansion_of_integer_identity
    orbitRadix_integer_identity

end AffineSymplecticOrbitCertificate

end ConnesRigidity
