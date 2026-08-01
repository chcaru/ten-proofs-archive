


import ConnesRigidity.GroupRingCertificateAlgebra
import ConnesRigidity.PropertyTExactCertificateOrbitBasis
import ConnesRigidity.PropertyTExactCertificateOrbitData
import ConnesRigidity.PropertyTExactCertificateOrbitGeneratorEnumeration












namespace ConnesRigidity.AffineSymplecticOrbitCertificate

universe u

set_option maxRecDepth 1000000

variable {G : Type u} [Group G]

noncomputable local instance orbitTargetDecidableEq : DecidableEq G :=
  Classical.decEq G


noncomputable def targetGroupIndicator (left right : G) : Int :=
  if left = right then 1 else 0


noncomputable def targetGeneratorMultiplicity
    (generators : Finset G) (element : G) : Int :=
  ∑ generator ∈ generators, targetGroupIndicator generator element



noncomputable def targetProductMultiplicity
    (generators : Finset G) (element : G) : Int :=
  ∑ left ∈ generators, ∑ right ∈ generators,
    targetGroupIndicator (right * left) element



theorem customaryLaplacian_coeff
    (generators : Finset G) (element : G) :
    (RationalGroupRing.customaryLaplacian generators).coeff element =
      (generators.card : ℚ) *
          (targetGroupIndicator (1 : G) element : ℚ) -
        (targetGeneratorMultiplicity generators element : ℚ) := by
  classical
  simp [RationalGroupRing.customaryLaplacian,
    RationalGroupRing.difference, targetGroupIndicator,
    targetGeneratorMultiplicity, Finsupp.single_apply,
    Finset.sum_sub_distrib]



theorem customaryLaplacian_mul_self_coeff
    (generators : Finset G) (element : G) :
    (RationalGroupRing.customaryLaplacian generators *
        RationalGroupRing.customaryLaplacian generators).coeff element =
      (generators.card : ℚ) ^ 2 *
          (targetGroupIndicator (1 : G) element : ℚ) -
        2 * (generators.card : ℚ) *
          (targetGeneratorMultiplicity generators element : ℚ) +
        (targetProductMultiplicity generators element : ℚ) := by
  classical
  simp [RationalGroupRing.customaryLaplacian,
    RationalGroupRing.difference, Finset.sum_mul, Finset.mul_sum,
    sub_mul, mul_sub, MonoidAlgebra.single_mul_single,
    targetGroupIndicator, targetGeneratorMultiplicity,
    targetProductMultiplicity, Finsupp.single_apply,
    Finset.sum_sub_distrib]
  split_ifs <;> ring




def targetWitnessValue
    (identityMultiplicity generatorMultiplicity productMultiplicity : Int) : Int :=
  64000000000000 *
      (576 * identityMultiplicity - 48 * generatorMultiplicity +
        productMultiplicity) -
    640000000000 * (24 * identityMultiplicity - generatorMultiplicity)




theorem scaledCustomarySpectralTarget_coeff
    (generators : Finset G) (element : G)
    (hcard : generators.card = 24) :
    ((certificateDenominator : ℚ) •
        ((4 : ℚ) •
            (RationalGroupRing.customaryLaplacian generators *
              RationalGroupRing.customaryLaplacian generators) -
          (1 / 25 : ℚ) •
            RationalGroupRing.customaryLaplacian generators)).coeff element =
      (targetWitnessValue
        (targetGroupIndicator (1 : G) element)
        (targetGeneratorMultiplicity generators element)
        (targetProductMultiplicity generators element) : ℚ) := by
  classical
  change
    (certificateDenominator : ℚ) *
        (4 *
            (RationalGroupRing.customaryLaplacian generators *
              RationalGroupRing.customaryLaplacian generators).coeff element -
          (1 / 25 : ℚ) *
            (RationalGroupRing.customaryLaplacian generators).coeff element) =
      _
  rw [customaryLaplacian_mul_self_coeff,
    customaryLaplacian_coeff, hcard]
  norm_num [certificateDenominator, targetWitnessValue]
  ring



theorem mem_scaledCustomarySpectralTarget_support
    (generators : Finset G) (element : G)
    (hcard : generators.card = 24)
    (hsupport : element ∈
      (((certificateDenominator : ℚ) •
        ((4 : ℚ) •
            (RationalGroupRing.customaryLaplacian generators *
              RationalGroupRing.customaryLaplacian generators) -
          (1 / 25 : ℚ) •
            RationalGroupRing.customaryLaplacian generators)).coeff.support)) :
    element = 1 ∨ element ∈ generators ∨
      ∃ left ∈ generators, ∃ right ∈ generators, right * left = element := by
  classical
  by_contra hmissing
  push Not at hmissing
  obtain ⟨hidentity, hgenerator, hproduct⟩ := hmissing
  have hidentityMultiplicity : targetGroupIndicator (1 : G) element = 0 := by
    simp [targetGroupIndicator, Ne.symm hidentity]
  have hgeneratorMultiplicity :
      targetGeneratorMultiplicity generators element = 0 := by
    unfold targetGeneratorMultiplicity
    apply Finset.sum_eq_zero
    intro generator hgenerator_mem
    simp [targetGroupIndicator,
      show generator ≠ element by
        intro heq
        exact hgenerator (heq ▸ hgenerator_mem)]
  have hproductMultiplicity :
      targetProductMultiplicity generators element = 0 := by
    unfold targetProductMultiplicity
    apply Finset.sum_eq_zero
    intro left hleft
    apply Finset.sum_eq_zero
    intro right hright
    simp [targetGroupIndicator, hproduct left hleft right hright]
  have hnonzero := Finsupp.mem_support_iff.mp hsupport
  rw [scaledCustomarySpectralTarget_coeff generators element hcard,
    hidentityMultiplicity, hgeneratorMultiplicity,
    hproductMultiplicity] at hnonzero
  norm_num [targetWitnessValue] at hnonzero




theorem scaledCustomarySpectralTarget_support_covered_by_basis
    {ι : Type*} (basis : ι → G)
    (generators : Finset G) (element : G)
    (hcard : generators.card = 24)
    (hinverse : generators.image Inv.inv = generators)
    (hone : ∃ index, basis index = 1)
    (hbasis : ∀ generator ∈ generators, ∃ index, basis index = generator)
    (hsupport : element ∈
      (((certificateDenominator : ℚ) •
        ((4 : ℚ) •
            (RationalGroupRing.customaryLaplacian generators *
              RationalGroupRing.customaryLaplacian generators) -
          (1 / 25 : ℚ) •
            RationalGroupRing.customaryLaplacian generators)).coeff.support)) :
    ∃ left right, (basis left)⁻¹ * basis right = element := by
  classical
  rcases mem_scaledCustomarySpectralTarget_support
    generators element hcard hsupport with hidentity | hgenerator | hproduct
  · obtain ⟨index, hindex⟩ := hone
    exact ⟨index, index, by simp [hindex, hidentity]⟩
  · obtain ⟨left, hleft⟩ := hone
    obtain ⟨right, hright⟩ := hbasis element hgenerator
    exact ⟨left, right, by simp [hleft, hright]⟩
  · obtain ⟨left, hleft, right, hright, hproduct⟩ := hproduct
    have hinvright : right⁻¹ ∈ generators := by
      rw [← hinverse]
      exact Finset.mem_image.mpr ⟨right, hright, rfl⟩
    obtain ⟨leftIndex, hleftIndex⟩ := hbasis right⁻¹ hinvright
    obtain ⟨rightIndex, hrightIndex⟩ := hbasis left hleft
    refine ⟨leftIndex, rightIndex, ?_⟩
    simp [hleftIndex, hrightIndex, hproduct]


noncomputable def orbitTargetWitnessIdentity (orbit : Nat) : Int :=
  dataEntry coefficientTargetWitnessData orbit 0


noncomputable def orbitTargetWitnessGeneratorMultiplicity
    (orbit : Nat) : Int :=
  dataEntry coefficientTargetWitnessData orbit 1



noncomputable def orbitTargetWitnessProductMultiplicity
    (orbit : Nat) : Int :=
  dataEntry coefficientTargetWitnessData orbit 2


def orbitTargetArithmeticRowCheck
    (witness target : Array Int) : Bool :=
  decide
    (targetWitnessValue (witness.getD 0 0)
        (witness.getD 1 0) (witness.getD 2 0) =
      target.getD 0 0)



noncomputable def orbitTargetArithmeticCheck : Bool :=
  decide (coefficientTargetWitnessData.size = 995) &&
    decide (coefficientTargetData.size = 995) &&
    (coefficientTargetWitnessData.toList.zip
      coefficientTargetData.toList).all fun rows =>
        orbitTargetArithmeticRowCheck rows.1 rows.2




theorem orbitTargetArithmeticCheck_valid :
    orbitTargetArithmeticCheck = true := by
  unfold orbitTargetArithmeticCheck orbitTargetArithmeticRowCheck
    targetWitnessValue coefficientTargetWitnessData coefficientTargetData
  decide +kernel



theorem orbitTargetArithmeticCheck_sound (orbit : Fin 995) :
    targetWitnessValue
        (orbitTargetWitnessIdentity orbit.val)
        (orbitTargetWitnessGeneratorMultiplicity orbit.val)
        (orbitTargetWitnessProductMultiplicity orbit.val) =
      coefficientOrbitTarget orbit.val := by
  have hcheck := orbitTargetArithmeticCheck_valid
  simp only [orbitTargetArithmeticCheck, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  obtain ⟨⟨hwitnessSize, htargetSize⟩, hrows⟩ := hcheck
  have hwitnessIndex : orbit.val < coefficientTargetWitnessData.size := by
    omega
  have htargetIndex : orbit.val < coefficientTargetData.size := by
    omega
  have hzip : orbit.val <
      (coefficientTargetWitnessData.toList.zip
        coefficientTargetData.toList).length := by
    simp only [List.length_zip, Array.length_toList]
    omega
  have hrow := List.all_eq_true.mp hrows _ (List.getElem_mem hzip)
  simp only [orbitTargetArithmeticRowCheck, decide_eq_true_eq,
    List.getElem_zip, Array.getElem_toList] at hrow
  simpa [orbitTargetWitnessIdentity,
    orbitTargetWitnessGeneratorMultiplicity,
    orbitTargetWitnessProductMultiplicity, coefficientOrbitTarget,
    dataEntry, Array.getD, hwitnessIndex, htargetIndex] using hrow





theorem orbitTargetRepresentative_coeff_of_witness
    (orbit : Fin 995)
    (hcard : gammaZeroElementaryGenerators.card = 24)
    (hidentity :
      targetGroupIndicator (1 : constructedGammaZeroGroup)
          (coefficientRepresentativeElement orbit.val) =
        orbitTargetWitnessIdentity orbit.val)
    (hgenerator :
      targetGeneratorMultiplicity gammaZeroElementaryGenerators
          (coefficientRepresentativeElement orbit.val) =
        orbitTargetWitnessGeneratorMultiplicity orbit.val)
    (hproduct :
      targetProductMultiplicity gammaZeroElementaryGenerators
          (coefficientRepresentativeElement orbit.val) =
        orbitTargetWitnessProductMultiplicity orbit.val)
    (harithmetic :
      targetWitnessValue
          (orbitTargetWitnessIdentity orbit.val)
          (orbitTargetWitnessGeneratorMultiplicity orbit.val)
          (orbitTargetWitnessProductMultiplicity orbit.val) =
        coefficientOrbitTarget orbit.val) :
    ((certificateDenominator : ℚ) •
        ((4 : ℚ) •
            (RationalGroupRing.customaryLaplacian
              gammaZeroElementaryGenerators *
              RationalGroupRing.customaryLaplacian
                gammaZeroElementaryGenerators) -
          (1 / 25 : ℚ) •
            RationalGroupRing.customaryLaplacian
              gammaZeroElementaryGenerators)).coeff
        (coefficientRepresentativeElement orbit.val) =
      (coefficientOrbitTarget orbit.val : ℚ) := by
  rw [scaledCustomarySpectralTarget_coeff
    gammaZeroElementaryGenerators
    (coefficientRepresentativeElement orbit.val) hcard,
    hidentity, hgenerator, hproduct, harithmetic]




theorem orbitTargetRepresentative_coeff_of_semantic_witness
    (orbit : Fin 995)
    (hidentity :
      targetGroupIndicator (1 : constructedGammaZeroGroup)
          (coefficientRepresentativeElement orbit.val) =
        orbitTargetWitnessIdentity orbit.val)
    (hgenerator :
      targetGeneratorMultiplicity gammaZeroElementaryGenerators
          (coefficientRepresentativeElement orbit.val) =
        orbitTargetWitnessGeneratorMultiplicity orbit.val)
    (hproduct :
      targetProductMultiplicity gammaZeroElementaryGenerators
          (coefficientRepresentativeElement orbit.val) =
        orbitTargetWitnessProductMultiplicity orbit.val) :
    ((certificateDenominator : ℚ) •
        ((4 : ℚ) •
            (RationalGroupRing.customaryLaplacian
              gammaZeroElementaryGenerators *
              RationalGroupRing.customaryLaplacian
                gammaZeroElementaryGenerators) -
          (1 / 25 : ℚ) •
            RationalGroupRing.customaryLaplacian
              gammaZeroElementaryGenerators)).coeff
        (coefficientRepresentativeElement orbit.val) =
      (coefficientOrbitTarget orbit.val : ℚ) :=
  orbitTargetRepresentative_coeff_of_witness orbit
    gammaZeroElementaryGenerators_card hidentity hgenerator hproduct
      (orbitTargetArithmeticCheck_sound orbit)

private theorem orbitTarget_generators_inverse_closed :
    gammaZeroElementaryGenerators.image Inv.inv =
      gammaZeroElementaryGenerators := by
  classical
  ext element
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨generator, hgenerator, rfl⟩
    simp only [gammaZeroElementaryGenerators, Finset.mem_union,
      Finset.mem_image] at hgenerator ⊢
    rcases hgenerator with hgenerator | ⟨other, hother, rfl⟩
    · exact Or.inr ⟨generator, hgenerator, rfl⟩
    · simpa using Or.inl hother
  · intro helement
    refine ⟨element⁻¹, ?_, by simp⟩
    simp only [gammaZeroElementaryGenerators, Finset.mem_union,
      Finset.mem_image] at helement ⊢
    rcases helement with helement | ⟨generator, hgenerator, rfl⟩
    · exact Or.inr ⟨element, helement, rfl⟩
    · simpa using Or.inl hgenerator





theorem orbitTarget_support_covered_by_basis
    (element : constructedGammaZeroGroup)
    (hsupport : element ∈
      (((certificateDenominator : ℚ) •
        ((4 : ℚ) •
            (RationalGroupRing.customaryLaplacian
              gammaZeroElementaryGenerators *
              RationalGroupRing.customaryLaplacian
                gammaZeroElementaryGenerators) -
          (1 / 25 : ℚ) •
            RationalGroupRing.customaryLaplacian
              gammaZeroElementaryGenerators)).coeff.support)) :
    ∃ left right : Fin 425,
      (orbitBasis left)⁻¹ * orbitBasis right = element := by
  apply scaledCustomarySpectralTarget_support_covered_by_basis
    orbitBasis gammaZeroElementaryGenerators element
      gammaZeroElementaryGenerators_card
  · exact orbitTarget_generators_inverse_closed
  · exact ⟨0, orbitBasis_zero⟩
  · exact generator_mem_orbitBasis
  · exact hsupport

end ConnesRigidity.AffineSymplecticOrbitCertificate
