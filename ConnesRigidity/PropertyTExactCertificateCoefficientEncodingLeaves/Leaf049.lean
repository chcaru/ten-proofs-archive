


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part049A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part049B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf049.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_049 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf049.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_049 :
    coefficientCheckData (coefficientNegativeTermChunk 6) =
      (coefficientSourceEncoding_049,
        8368620896) := by
  rw [show coefficientNegativeTermChunk 6 =
      (coefficientNegativeTermChunk 6).take 2000 ++
        (coefficientNegativeTermChunk 6).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_049_a,
    coefficientEncodingLeafCheck_049_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_049
    coefficientSourceEncoding_049_a
    coefficientSourceEncoding_049_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
