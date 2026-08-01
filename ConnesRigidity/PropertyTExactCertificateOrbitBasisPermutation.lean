


import ConnesRigidity.PropertyTExactCertificateOrbitBasisTransportValidation










namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open Matrix
open scoped BigOperators

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0



def orbitBasisFingerprintWeight (index : Fin 20) : Int :=
  #[568241, -995326, 701956, 449052, 83124,
    68454, 579923, -189473, -162127, 539463,
    678925, -902206, -6188, -399102, 642882,
    -300777, 480068, 918894, 754901, -401632].getD index.val 0


def orbitBasisRowFingerprint (row : Array Int) : Int :=
  ∑ index : Fin 20,
    orbitBasisFingerprintWeight index * row.getD index.val 0



theorem orbitBasisFingerprints_nodup :
    (basisData.toList.map orbitBasisRowFingerprint).Nodup := by
  decide +kernel


theorem orbitBasisRows_symplectic (index : Fin 425) :
    isSymplecticRow (basisData.getD index.val #[]) = true := by
  have hindex : index.val < basisData.size := by
    simp [orbitBasisData_size]
  have hrows : basisData.toList.all isSymplecticRow = true := by
    simpa [basisRowsSymplecticCheck] using
      orbitBasisRowsSymplecticCheck_valid
  have hrow := List.all_eq_true.mp hrows basisData[index.val]
    (by simp)
  simpa [Array.getD_eq_getD_getElem?, hindex] using hrow



theorem orbitBasis_injective : Function.Injective orbitBasis := by
  intro left right heq
  have hleft := orbitBasisRows_symplectic left
  have hright := orbitBasisRows_symplectic right
  have hraw : rawRowEq (basisData.getD left.val #[])
      (basisData.getD right.val #[]) = true :=
    (rawRowEq_iff_gammaZeroOfRow hleft hright).2 heq
  have hfingerprint :
      orbitBasisRowFingerprint (basisData.getD left.val #[]) =
        orbitBasisRowFingerprint (basisData.getD right.val #[]) := by
    unfold orbitBasisRowFingerprint
    apply Finset.sum_congr rfl
    intro index _
    congr 1
    exact rawRowEq_getD hraw index.isLt
  have hleftIndex : left.val <
      (basisData.toList.map orbitBasisRowFingerprint).length := by
    simp [orbitBasisData_size]
  have hrightIndex : right.val <
      (basisData.toList.map orbitBasisRowFingerprint).length := by
    simp [orbitBasisData_size]
  apply Fin.ext
  apply (orbitBasisFingerprints_nodup.getElem_inj_iff
    (i := left.val) (hi := hleftIndex)
    (j := right.val) (hj := hrightIndex)).mp
  simpa [Array.getD_eq_getD_getElem?, orbitBasisData_size,
    left.isLt, right.isLt] using hfingerprint


noncomputable def orbitBasisPermutation (symmetry : OrbitSymmetry)
    (index : Fin 425) : Fin 425 :=
  ⟨symmetryBasisImage symmetry.index.val index.val,
    symmetryBasisImage_lt symmetry.index index⟩

@[simp] theorem orbitBasisPermutation_val (symmetry : OrbitSymmetry)
    (index : Fin 425) :
    (orbitBasisPermutation symmetry index).val =
      symmetryBasisImage symmetry.index.val index.val := rfl



theorem orbitBasisPermutation_apply_basis (symmetry : OrbitSymmetry)
    (index : Fin 425) :
    orbitBasis (orbitBasisPermutation symmetry index) =
      orbitSymmetry symmetry.index (orbitBasis index) :=
  (orbitSymmetry_basis symmetry index).symm



@[simp] theorem orbitBasisPermutation_one (index : Fin 425) :
    orbitBasisPermutation 1 index = index := by
  apply orbitBasis_injective
  rw [orbitBasisPermutation_apply_basis,
    OrbitSymmetry.automorphism_one]
  rfl



theorem orbitBasisPermutation_mul (left right : OrbitSymmetry)
    (index : Fin 425) :
    orbitBasisPermutation (left * right) index =
      orbitBasisPermutation left (orbitBasisPermutation right index) := by
  apply orbitBasis_injective
  rw [orbitBasisPermutation_apply_basis,
    orbitBasisPermutation_apply_basis,
    orbitBasisPermutation_apply_basis,
    orbitSymmetry_mul]
  rfl



instance orbitBasisMulAction : MulAction OrbitSymmetry (Fin 425) where
  smul := orbitBasisPermutation
  one_smul := orbitBasisPermutation_one
  mul_smul := orbitBasisPermutation_mul



@[simp] theorem orbitBasis_smul_val (symmetry : OrbitSymmetry)
    (index : Fin 425) :
    (symmetry • index).val =
      symmetryBasisImage symmetry.index.val index.val := rfl



@[simp] theorem orbitBasis_smul (symmetry : OrbitSymmetry)
    (index : Fin 425) :
    orbitBasis (symmetry • index) = symmetry • orbitBasis index :=
  orbitBasisPermutation_apply_basis symmetry index



theorem orbitSymmetry_basis_action (symmetry : OrbitSymmetry)
    (index : Fin 425) :
    orbitSymmetry symmetry.index (orbitBasis index) =
      orbitBasis (symmetry • index) :=
  (orbitBasis_smul symmetry index).symm



noncomputable def orbitBasisPermutationEquiv (symmetry : OrbitSymmetry) :
    Equiv.Perm (Fin 425) :=
  MulAction.toPerm symmetry

@[simp] theorem orbitBasisPermutationEquiv_apply (symmetry : OrbitSymmetry)
    (index : Fin 425) :
    orbitBasisPermutationEquiv symmetry index =
      orbitBasisPermutation symmetry index := rfl



noncomputable def orbitBasisPermutationHom :
    OrbitSymmetry →* Equiv.Perm (Fin 425) :=
  MulAction.toPermHom OrbitSymmetry (Fin 425)

@[simp] theorem orbitBasisPermutationHom_apply (symmetry : OrbitSymmetry)
    (index : Fin 425) :
    orbitBasisPermutationHom symmetry index =
      orbitBasisPermutation symmetry index := rfl

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
