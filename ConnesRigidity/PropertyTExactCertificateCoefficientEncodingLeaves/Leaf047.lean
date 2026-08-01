
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part047A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part047B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf047.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_047 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf047.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_047 :
    coefficientCheckData (coefficientNegativeTermChunk 4) =
      (coefficientSourceEncoding_047,
        8675490560) := by
  rw [show coefficientNegativeTermChunk 4 =
      (coefficientNegativeTermChunk 4).take 2000 ++
        (coefficientNegativeTermChunk 4).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_047_a,
    coefficientEncodingLeafCheck_047_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_047
    coefficientSourceEncoding_047_a
    coefficientSourceEncoding_047_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
