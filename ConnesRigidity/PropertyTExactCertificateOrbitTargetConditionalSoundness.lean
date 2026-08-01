


import ConnesRigidity.PropertyTExactCertificateOrbitTargetProductSemantics
import ConnesRigidity.PropertyTExactCertificateOrbitTargetRepresentativeSoundness









namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section



theorem orbitTargetRepresentative_coeff_of_streaming_check
    (orbit : Fin 995) (hcheck : orbitTargetStreamingCheck = true) :
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
  obtain ⟨hrecordsLength, hinversesLength, hrowsLength, hinverseRowsLength,
    _, _, _, hrecords, hinverses, hinverseRows, _, hrows⟩ :=
      orbitTargetStreamingCheck_sound hcheck
  have hrepresentative := orbitTargetRepresentativeRowsCheck_orbit orbit
    hinverseRowsLength hrowsLength hinverseRows hrows
  obtain ⟨hsize, hbounded, hvalid, _, _, _, _⟩ := hrepresentative
  have hsemantic := orbitTargetRepresentativeWitness_semantics orbit hcheck
  apply orbitTargetRepresentative_coeff_of_semantic_witness orbit
    hsemantic.1 hsemantic.2.1
  have hproducts := orbitTargetProductRecords_countP_eq_targetProductMultiplicity
    (coefficientRepresentativeData.getD orbit.val #[])
      hsize hvalid hbounded hrecordsLength hinversesLength
      hrecords hinverses
  change
    targetProductMultiplicity gammaZeroElementaryGenerators
      (gammaZeroOfRow
        (coefficientRepresentativeData.getD orbit.val #[])) =
      orbitTargetWitnessProductMultiplicity orbit.val
  exact hproducts.symm.trans hsemantic.2.2

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
