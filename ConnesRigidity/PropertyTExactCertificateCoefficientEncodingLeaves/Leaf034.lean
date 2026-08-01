


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part034A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part034B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf034.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_034 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf034.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_034 :
    coefficientCheckData (coefficientFactorTermChunk034) =
      (coefficientSourceEncoding_034,
        880423612434672) := by
  rw [show coefficientFactorTermChunk034 =
      (coefficientFactorTermChunk034).take 2125 ++
        (coefficientFactorTermChunk034).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_034_a,
    coefficientEncodingLeafCheck_034_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_034
    coefficientSourceEncoding_034_a
    coefficientSourceEncoding_034_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
