


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part051A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part051B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf051.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_051 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf051.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_051 :
    coefficientCheckData (coefficientNegativeTermChunk 8) =
      (coefficientSourceEncoding_051,
        9345289824) := by
  rw [show coefficientNegativeTermChunk 8 =
      (coefficientNegativeTermChunk 8).take 2000 ++
        (coefficientNegativeTermChunk 8).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_051_a,
    coefficientEncodingLeafCheck_051_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_051
    coefficientSourceEncoding_051_a
    coefficientSourceEncoding_051_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
