


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part059A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part059B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf059.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_059 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf059.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_059 :
    coefficientCheckData (coefficientNegativeTermChunk 16) =
      (coefficientSourceEncoding_059,
        7125016384) := by
  rw [show coefficientNegativeTermChunk 16 =
      (coefficientNegativeTermChunk 16).take 2000 ++
        (coefficientNegativeTermChunk 16).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_059_a,
    coefficientEncodingLeafCheck_059_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_059
    coefficientSourceEncoding_059_a
    coefficientSourceEncoding_059_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
