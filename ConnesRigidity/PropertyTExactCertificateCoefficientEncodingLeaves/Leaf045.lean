


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part045A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part045B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf045.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_045 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf045.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_045 :
    coefficientCheckData (coefficientNegativeTermChunk 2) =
      (coefficientSourceEncoding_045,
        9328672928) := by
  rw [show coefficientNegativeTermChunk 2 =
      (coefficientNegativeTermChunk 2).take 2000 ++
        (coefficientNegativeTermChunk 2).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_045_a,
    coefficientEncodingLeafCheck_045_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_045
    coefficientSourceEncoding_045_a
    coefficientSourceEncoding_045_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
