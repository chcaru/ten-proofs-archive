


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientTarget.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientTargetEncoding :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientTarget.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientTargetEncodingCheck :
    coefficientCheckData targetTerms =
      (coefficientTargetEncoding, 18435840000000000) := by
  unfold coefficientCheckData coefficientTargetEncoding
  unfold targetTerms customaryLaplacianEntries integerOuterTerms
    basisIndex tableIndex productIndex productIndexDataRow
  unfold productIndexDataRow000
    productIndexDataRow001
    productIndexDataRow002
    productIndexDataRow003
    productIndexDataRow004
    productIndexDataRow005
    productIndexDataRow006
    productIndexDataRow007
    productIndexDataRow008
    productIndexDataRow009
    productIndexDataRow010
    productIndexDataRow011
    productIndexDataRow012
    productIndexDataRow013
    productIndexDataRow014
    productIndexDataRow015
    productIndexDataRow016
    productIndexDataRow017
    productIndexDataRow018
    productIndexDataRow019
    productIndexDataRow020
    productIndexDataRow021
    productIndexDataRow022
    productIndexDataRow023
    productIndexDataRow024
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
