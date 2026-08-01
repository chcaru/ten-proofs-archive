
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalLexSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedValidation
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalInverseSemantics

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

theorem coefficientCanonicalCoordinates_representative
    (orbit : Fin 995) :
    ∃ canonical : List Int,
      coefficientCanonicalCoordinates
          (coefficientRepresentativeElement orbit.val) =
            canonical.reverse ∧
        targetCoordinateCode canonical =
          (coefficientCanonicalWitnessData.getD orbit.val []).getD 1 0 :=
  coefficientCanonicalCoordinates_representative_of_row_check orbit
    (coefficientCanonicalRepresentative_valid orbit)
    (coefficientCanonicalRepresentative_inverse orbit)
    (coefficientCanonicalWitnessRowCheck_valid orbit)

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
