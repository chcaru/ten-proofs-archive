
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part061A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part061B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf061.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_061 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf061.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_061 :
    coefficientCheckData (coefficientNegativeTermChunk 18) =
      (coefficientSourceEncoding_061,
        7272996512) := by
  rw [show coefficientNegativeTermChunk 18 =
      (coefficientNegativeTermChunk 18).take 2000 ++
        (coefficientNegativeTermChunk 18).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_061_a,
    coefficientEncodingLeafCheck_061_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_061
    coefficientSourceEncoding_061_a
    coefficientSourceEncoding_061_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
