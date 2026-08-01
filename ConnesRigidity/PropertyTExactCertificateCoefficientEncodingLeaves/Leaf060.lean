
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part060A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part060B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf060.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_060 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf060.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_060 :
    coefficientCheckData (coefficientNegativeTermChunk 17) =
      (coefficientSourceEncoding_060,
        7864677152) := by
  rw [show coefficientNegativeTermChunk 17 =
      (coefficientNegativeTermChunk 17).take 2000 ++
        (coefficientNegativeTermChunk 17).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_060_a,
    coefficientEncodingLeafCheck_060_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_060
    coefficientSourceEncoding_060_a
    coefficientSourceEncoding_060_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
