


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part077A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part077B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf077.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_077 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf077.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_077 :
    coefficientCheckData (coefficientPositiveTermChunk 14) =
      (coefficientSourceEncoding_077,
        30787484800) := by
  rw [show coefficientPositiveTermChunk 14 =
      (coefficientPositiveTermChunk 14).take 4500 ++
        (coefficientPositiveTermChunk 14).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_077_a,
    coefficientEncodingLeafCheck_077_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_077
    coefficientSourceEncoding_077_a
    coefficientSourceEncoding_077_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
