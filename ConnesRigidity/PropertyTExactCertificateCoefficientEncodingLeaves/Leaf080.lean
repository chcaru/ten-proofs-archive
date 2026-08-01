


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part080A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part080B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf080.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_080 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf080.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_080 :
    coefficientCheckData (coefficientPositiveTermChunk 17) =
      (coefficientSourceEncoding_080,
        5004272384) := by
  rw [show coefficientPositiveTermChunk 17 =
      (coefficientPositiveTermChunk 17).take 643 ++
        (coefficientPositiveTermChunk 17).drop 643 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_080_a,
    coefficientEncodingLeafCheck_080_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_080
    coefficientSourceEncoding_080_a
    coefficientSourceEncoding_080_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
