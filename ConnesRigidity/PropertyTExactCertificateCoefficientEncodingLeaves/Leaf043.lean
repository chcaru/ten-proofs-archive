
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part043A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part043B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf043.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_043 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf043.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_043 :
    coefficientCheckData (coefficientNegativeTermChunk 0) =
      (coefficientSourceEncoding_043,
        59664338176) := by
  rw [show coefficientNegativeTermChunk 0 =
      (coefficientNegativeTermChunk 0).take 2000 ++
        (coefficientNegativeTermChunk 0).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_043_a,
    coefficientEncodingLeafCheck_043_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_043
    coefficientSourceEncoding_043_a
    coefficientSourceEncoding_043_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
