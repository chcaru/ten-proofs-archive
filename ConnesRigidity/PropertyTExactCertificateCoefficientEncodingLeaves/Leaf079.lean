


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part079A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part079B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf079.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_079 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf079.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_079 :
    coefficientCheckData (coefficientPositiveTermChunk 16) =
      (coefficientSourceEncoding_079,
        35234008064) := by
  rw [show coefficientPositiveTermChunk 16 =
      (coefficientPositiveTermChunk 16).take 4500 ++
        (coefficientPositiveTermChunk 16).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_079_a,
    coefficientEncodingLeafCheck_079_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_079
    coefficientSourceEncoding_079_a
    coefficientSourceEncoding_079_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
