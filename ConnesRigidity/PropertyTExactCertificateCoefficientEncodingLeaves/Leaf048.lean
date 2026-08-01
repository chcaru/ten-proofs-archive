


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part048A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part048B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf048.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_048 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf048.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_048 :
    coefficientCheckData (coefficientNegativeTermChunk 5) =
      (coefficientSourceEncoding_048,
        8284270880) := by
  rw [show coefficientNegativeTermChunk 5 =
      (coefficientNegativeTermChunk 5).take 2000 ++
        (coefficientNegativeTermChunk 5).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_048_a,
    coefficientEncodingLeafCheck_048_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_048
    coefficientSourceEncoding_048_a
    coefficientSourceEncoding_048_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
