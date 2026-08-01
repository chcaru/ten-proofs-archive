


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part053A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part053B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf053.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_053 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf053.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_053 :
    coefficientCheckData (coefficientNegativeTermChunk 10) =
      (coefficientSourceEncoding_053,
        7864616160) := by
  rw [show coefficientNegativeTermChunk 10 =
      (coefficientNegativeTermChunk 10).take 2000 ++
        (coefficientNegativeTermChunk 10).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_053_a,
    coefficientEncodingLeafCheck_053_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_053
    coefficientSourceEncoding_053_a
    coefficientSourceEncoding_053_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
