
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part058A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part058B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf058.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_058 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf058.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_058 :
    coefficientCheckData (coefficientNegativeTermChunk 15) =
      (coefficientSourceEncoding_058,
        7262208512) := by
  rw [show coefficientNegativeTermChunk 15 =
      (coefficientNegativeTermChunk 15).take 2000 ++
        (coefficientNegativeTermChunk 15).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_058_a,
    coefficientEncodingLeafCheck_058_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_058
    coefficientSourceEncoding_058_a
    coefficientSourceEncoding_058_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
