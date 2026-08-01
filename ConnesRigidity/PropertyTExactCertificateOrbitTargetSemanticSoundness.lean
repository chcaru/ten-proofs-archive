


import ConnesRigidity.PropertyTExactCertificateOrbitTargetConditionalSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitTargetValidation










namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section



theorem orbitTargetRepresentative_coeff (orbit : Fin 995) :
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
  orbitTargetRepresentative_coeff_of_streaming_check orbit
    orbitTargetStreamingCheck_valid

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
