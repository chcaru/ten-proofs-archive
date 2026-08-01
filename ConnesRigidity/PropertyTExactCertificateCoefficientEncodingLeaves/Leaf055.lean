


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part055A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part055B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf055.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_055 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf055.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_055 :
    coefficientCheckData (coefficientNegativeTermChunk 12) =
      (coefficientSourceEncoding_055,
        9042638912) := by
  rw [show coefficientNegativeTermChunk 12 =
      (coefficientNegativeTermChunk 12).take 2000 ++
        (coefficientNegativeTermChunk 12).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_055_a,
    coefficientEncodingLeafCheck_055_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_055
    coefficientSourceEncoding_055_a
    coefficientSourceEncoding_055_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
