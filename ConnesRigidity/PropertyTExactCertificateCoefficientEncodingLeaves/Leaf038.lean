


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part038A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part038B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf038.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_038 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf038.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_038 :
    coefficientCheckData (coefficientFactorTermChunk038) =
      (coefficientSourceEncoding_038,
        1040566141762576) := by
  rw [show coefficientFactorTermChunk038 =
      (coefficientFactorTermChunk038).take 2125 ++
        (coefficientFactorTermChunk038).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_038_a,
    coefficientEncodingLeafCheck_038_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_038
    coefficientSourceEncoding_038_a
    coefficientSourceEncoding_038_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
