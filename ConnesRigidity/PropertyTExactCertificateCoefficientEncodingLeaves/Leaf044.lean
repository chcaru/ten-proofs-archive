
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part044A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part044B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf044.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_044 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf044.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_044 :
    coefficientCheckData (coefficientNegativeTermChunk 1) =
      (coefficientSourceEncoding_044,
        32410187776) := by
  rw [show coefficientNegativeTermChunk 1 =
      (coefficientNegativeTermChunk 1).take 2000 ++
        (coefficientNegativeTermChunk 1).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_044_a,
    coefficientEncodingLeafCheck_044_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_044
    coefficientSourceEncoding_044_a
    coefficientSourceEncoding_044_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
