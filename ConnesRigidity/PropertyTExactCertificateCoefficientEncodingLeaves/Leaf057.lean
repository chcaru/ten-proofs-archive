


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part057A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part057B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf057.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_057 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf057.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_057 :
    coefficientCheckData (coefficientNegativeTermChunk 14) =
      (coefficientSourceEncoding_057,
        7403570816) := by
  rw [show coefficientNegativeTermChunk 14 =
      (coefficientNegativeTermChunk 14).take 2000 ++
        (coefficientNegativeTermChunk 14).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_057_a,
    coefficientEncodingLeafCheck_057_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_057
    coefficientSourceEncoding_057_a
    coefficientSourceEncoding_057_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
