
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part052A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part052B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf052.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_052 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf052.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_052 :
    coefficientCheckData (coefficientNegativeTermChunk 9) =
      (coefficientSourceEncoding_052,
        8896576384) := by
  rw [show coefficientNegativeTermChunk 9 =
      (coefficientNegativeTermChunk 9).take 2000 ++
        (coefficientNegativeTermChunk 9).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_052_a,
    coefficientEncodingLeafCheck_052_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_052
    coefficientSourceEncoding_052_a
    coefficientSourceEncoding_052_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
