
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part046A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part046B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf046.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_046 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf046.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_046 :
    coefficientCheckData (coefficientNegativeTermChunk 3) =
      (coefficientSourceEncoding_046,
        8509504576) := by
  rw [show coefficientNegativeTermChunk 3 =
      (coefficientNegativeTermChunk 3).take 2000 ++
        (coefficientNegativeTermChunk 3).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_046_a,
    coefficientEncodingLeafCheck_046_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_046
    coefficientSourceEncoding_046_a
    coefficientSourceEncoding_046_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
