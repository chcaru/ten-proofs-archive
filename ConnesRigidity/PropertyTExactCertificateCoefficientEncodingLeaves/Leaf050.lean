
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part050A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part050B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf050.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_050 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf050.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_050 :
    coefficientCheckData (coefficientNegativeTermChunk 7) =
      (coefficientSourceEncoding_050,
        10281946048) := by
  rw [show coefficientNegativeTermChunk 7 =
      (coefficientNegativeTermChunk 7).take 2000 ++
        (coefficientNegativeTermChunk 7).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_050_a,
    coefficientEncodingLeafCheck_050_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_050
    coefficientSourceEncoding_050_a
    coefficientSourceEncoding_050_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
