
import ConnesRigidity.GammaZeroGenerators
import ConnesRigidity.GroupRingCertificateAlgebra
import ConnesRigidity.PropertyTExactCertificateOrbitAlgebra
import ConnesRigidity.PropertyTExactCertificateOrbitAverage
import ConnesRigidity.PropertyTExactCertificateOrbitBlockCertificate
import ConnesRigidity.PropertyTExactCertificateOrbitBlockExpansion
import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitPositivity

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable local instance gammaZeroDecidableEq :
    DecidableEq constructedGammaZeroGroup :=
  Classical.decEq _

theorem gammaZeroElementaryGenerators_inverse_closed :
    gammaZeroElementaryGenerators.image Inv.inv =
      gammaZeroElementaryGenerators := by
  classical
  ext g
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simp only [gammaZeroElementaryGenerators, Finset.mem_union,
      Finset.mem_image] at hh ⊢
    rcases hh with hh | ⟨k, hk, rfl⟩
    · exact Or.inr ⟨h, hh, rfl⟩
    · simpa using Or.inl hk
  · intro hg
    refine ⟨g⁻¹, ?_, by simp⟩
    simp only [gammaZeroElementaryGenerators, Finset.mem_union,
      Finset.mem_image] at hg ⊢
    rcases hg with hg | ⟨h, hh, rfl⟩
    · exact Or.inr ⟨g, hg, rfl⟩
    · simpa using Or.inl hh

theorem spectralGapPolynomial_eq_customary :
    RationalGroupRing.laplacian gammaZeroElementaryGenerators *
          RationalGroupRing.laplacian gammaZeroElementaryGenerators -
        (1 / 50 : ℚ) •
          RationalGroupRing.laplacian gammaZeroElementaryGenerators =
      (4 : ℚ) •
          (RationalGroupRing.customaryLaplacian
            gammaZeroElementaryGenerators *
            RationalGroupRing.customaryLaplacian
              gammaZeroElementaryGenerators) -
        (1 / 25 : ℚ) •
          RationalGroupRing.customaryLaplacian
            gammaZeroElementaryGenerators := by
  classical
  rw [RationalGroupRing.laplacian_eq_two_smul_customaryLaplacian
    gammaZeroElementaryGenerators
    gammaZeroElementaryGenerators_inverse_closed]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  norm_num

theorem constructedGammaZero_hasKazhdanPropertyT_of_certificate
    {r : ℚ}
    (certificate : RationalGroupRing.HasSpectralGapCertificate
      gammaZeroElementaryGenerators r) :
    HasKazhdanPropertyT constructedGammaZeroGroup :=
  hasKazhdanPropertyT_of_spectralGapCertificate
    constructedGammaZeroGroup gammaZeroElementaryGenerators r
      gammaZeroElementaryGenerators_generate certificate

theorem exactSpectralGapCertificate_of_customary_identity
    {value : RationalGroupRing constructedGammaZeroGroup}
    (hpositive : RationalGroupRing.IsPositiveSumOfSquares value)
    (hidentity : value =
      (4 : ℚ) •
          (RationalGroupRing.customaryLaplacian
            gammaZeroElementaryGenerators *
            RationalGroupRing.customaryLaplacian
              gammaZeroElementaryGenerators) -
        (1 / 25 : ℚ) •
          RationalGroupRing.customaryLaplacian
            gammaZeroElementaryGenerators) :
    RationalGroupRing.HasSpectralGapCertificate
      gammaZeroElementaryGenerators (1 / 50) := by
  refine ⟨by norm_num, ?_⟩
  rw [spectralGapPolynomial_eq_customary]
  rw [← hidentity]
  exact hpositive

theorem fullGramExpansion_isPositiveSumOfSquares_of_reduced
    {n : ℕ}
    (basis : Fin (n + 1) → constructedGammaZeroGroup)
    (gram : Fin (n + 1) → Fin (n + 1) → ℚ)
    (hrow : ∀ i, ∑ j, gram i j = 0)
    (hcol : ∀ j, ∑ i, gram i j = 0)
    (hpositive : RationalGroupRing.IsPositiveSumOfSquares
      (OrbitPositivity.matrixAtomExpansion
        (reducedGroupAtom basis)
        (fun i j : Fin n => gram i.succ j.succ))) :
    RationalGroupRing.IsPositiveSumOfSquares
      (fullGramExpansion basis gram) := by
  rw [fullGramExpansion_eq_reduced_of_zero_sums basis gram hrow hcol]
  exact hpositive

theorem fullGramExpansion_isPositiveSumOfSquares_of_symmetric_reduced
    {n : ℕ}
    (basis : Fin (n + 1) → constructedGammaZeroGroup)
    (gram : Fin (n + 1) → Fin (n + 1) → ℚ)
    (hsymm : ∀ i j, gram i j = gram j i)
    (hrow : ∀ i, ∑ j, gram i j = 0)
    (hpositive : RationalGroupRing.IsPositiveSumOfSquares
      (OrbitPositivity.matrixAtomExpansion
        (reducedGroupAtom basis)
        (fun i j : Fin n => gram i.succ j.succ))) :
    RationalGroupRing.IsPositiveSumOfSquares
      (fullGramExpansion basis gram) := by
  apply fullGramExpansion_isPositiveSumOfSquares_of_reduced
    basis gram hrow _ hpositive
  intro j
  simpa only [hsymm] using hrow j

theorem exactSpectralGapCertificate_of_scaled_customary_identity
    {scale : ℚ} (hscale : 0 < scale)
    {value : RationalGroupRing constructedGammaZeroGroup}
    (hpositive : RationalGroupRing.IsPositiveSumOfSquares value)
    (hidentity : value = scale •
      ((4 : ℚ) •
          (RationalGroupRing.customaryLaplacian
            gammaZeroElementaryGenerators *
            RationalGroupRing.customaryLaplacian
              gammaZeroElementaryGenerators) -
        (1 / 25 : ℚ) •
          RationalGroupRing.customaryLaplacian
            gammaZeroElementaryGenerators)) :
    RationalGroupRing.HasSpectralGapCertificate
      gammaZeroElementaryGenerators (1 / 50) := by
  apply exactSpectralGapCertificate_of_customary_identity
    (value := scale⁻¹ • value)
  · exact RationalGroupRing.IsPositiveSumOfSquares.smul
      scale⁻¹ (inv_nonneg.mpr hscale.le) hpositive
  · rw [hidentity, smul_smul]
    simp [hscale.ne']

theorem constructedGammaZero_hasKazhdanPropertyT_of_customary_identity
    {value : RationalGroupRing constructedGammaZeroGroup}
    (hpositive : RationalGroupRing.IsPositiveSumOfSquares value)
    (hidentity : value =
      (4 : ℚ) •
          (RationalGroupRing.customaryLaplacian
            gammaZeroElementaryGenerators *
            RationalGroupRing.customaryLaplacian
              gammaZeroElementaryGenerators) -
        (1 / 25 : ℚ) •
          RationalGroupRing.customaryLaplacian
            gammaZeroElementaryGenerators) :
    HasKazhdanPropertyT constructedGammaZeroGroup :=
  constructedGammaZero_hasKazhdanPropertyT_of_certificate
    (exactSpectralGapCertificate_of_customary_identity hpositive hidentity)

theorem constructedGammaZero_hasKazhdanPropertyT_of_scaled_customary_identity
    {scale : ℚ} (hscale : 0 < scale)
    {value : RationalGroupRing constructedGammaZeroGroup}
    (hpositive : RationalGroupRing.IsPositiveSumOfSquares value)
    (hidentity : value = scale •
      ((4 : ℚ) •
          (RationalGroupRing.customaryLaplacian
            gammaZeroElementaryGenerators *
            RationalGroupRing.customaryLaplacian
              gammaZeroElementaryGenerators) -
        (1 / 25 : ℚ) •
          RationalGroupRing.customaryLaplacian
            gammaZeroElementaryGenerators)) :
    HasKazhdanPropertyT constructedGammaZeroGroup :=
  constructedGammaZero_hasKazhdanPropertyT_of_certificate
    (exactSpectralGapCertificate_of_scaled_customary_identity
      hscale hpositive hidentity)

theorem constructedGammaZero_hasKazhdanPropertyT_of_block_candidate_identity
    (hidentity : orbitBlockCandidate =
      (certificateDenominator : ℚ) •
        ((4 : ℚ) •
            (RationalGroupRing.customaryLaplacian
              gammaZeroElementaryGenerators *
              RationalGroupRing.customaryLaplacian
                gammaZeroElementaryGenerators) -
          (1 / 25 : ℚ) •
            RationalGroupRing.customaryLaplacian
              gammaZeroElementaryGenerators)) :
    HasKazhdanPropertyT constructedGammaZeroGroup := by
  apply constructedGammaZero_hasKazhdanPropertyT_of_scaled_customary_identity
    (scale := (certificateDenominator : ℚ))
  · norm_num [certificateDenominator]
  · exact orbitBlockCandidate_isPositiveSumOfSquares
  · exact hidentity

theorem constructedGammaZero_hasKazhdanPropertyT_of_orbit_gram_identity
    (hblock : orbitBlockCandidate =
      fullGramExpansion orbitBasis
        (fun i j : Fin 425 => (gramEntry i.val j.val : ℚ)))
    (hidentity :
      fullGramExpansion orbitBasis
          (fun i j : Fin 425 => (gramEntry i.val j.val : ℚ)) =
        (certificateDenominator : ℚ) •
          ((4 : ℚ) •
              (RationalGroupRing.customaryLaplacian
                gammaZeroElementaryGenerators *
                RationalGroupRing.customaryLaplacian
                  gammaZeroElementaryGenerators) -
            (1 / 25 : ℚ) •
              RationalGroupRing.customaryLaplacian
                gammaZeroElementaryGenerators)) :
    HasKazhdanPropertyT constructedGammaZeroGroup :=
  constructedGammaZero_hasKazhdanPropertyT_of_block_candidate_identity
    (hblock.trans hidentity)

theorem constructedGammaZero_hasKazhdanPropertyT :
    HasKazhdanPropertyT constructedGammaZeroGroup := by
  apply constructedGammaZero_hasKazhdanPropertyT_of_orbit_gram_identity
    orbitBlockCandidate_eq_fullGramExpansion
  simpa [orbitGramExpansion, orbitSpectralTarget] using
    orbitGramExpansion_eq_orbitSpectralTarget

theorem constructedGammaZero_hasKazhdanPropertyT_of_symmetric_scaled_gram
    {n : ℕ}
    (basis : Fin (n + 1) → constructedGammaZeroGroup)
    (gram : Fin (n + 1) → Fin (n + 1) → ℚ)
    (hsymm : ∀ i j, gram i j = gram j i)
    (hrow : ∀ i, ∑ j, gram i j = 0)
    (hpositive : RationalGroupRing.IsPositiveSumOfSquares
      (OrbitPositivity.matrixAtomExpansion
        (reducedGroupAtom basis)
        (fun i j : Fin n => gram i.succ j.succ)))
    {scale : ℚ} (hscale : 0 < scale)
    (hidentity : fullGramExpansion basis gram = scale •
      ((4 : ℚ) •
          (RationalGroupRing.customaryLaplacian
            gammaZeroElementaryGenerators *
            RationalGroupRing.customaryLaplacian
              gammaZeroElementaryGenerators) -
        (1 / 25 : ℚ) •
          RationalGroupRing.customaryLaplacian
            gammaZeroElementaryGenerators)) :
    HasKazhdanPropertyT constructedGammaZeroGroup :=
  constructedGammaZero_hasKazhdanPropertyT_of_scaled_customary_identity
    hscale
    (fullGramExpansion_isPositiveSumOfSquares_of_symmetric_reduced
      basis gram hsymm hrow hpositive)
    hidentity

end ConnesRigidity.AffineSymplecticOrbitCertificate
