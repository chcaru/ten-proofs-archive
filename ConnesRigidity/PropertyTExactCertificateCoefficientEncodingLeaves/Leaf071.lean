


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part071A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part071B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf071.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_071 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf071.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_071 :
    coefficientCheckData (coefficientPositiveTermChunk 8) =
      (coefficientSourceEncoding_071,
        36270701312) := by
  rw [show coefficientPositiveTermChunk 8 =
      (coefficientPositiveTermChunk 8).take 4500 ++
        (coefficientPositiveTermChunk 8).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_071_a,
    coefficientEncodingLeafCheck_071_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_071
    coefficientSourceEncoding_071_a
    coefficientSourceEncoding_071_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
