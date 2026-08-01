


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part064A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part064B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf064.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_064 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf064.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_064 :
    coefficientCheckData (coefficientPositiveTermChunk 1) =
      (coefficientSourceEncoding_064,
        57020960384) := by
  rw [show coefficientPositiveTermChunk 1 =
      (coefficientPositiveTermChunk 1).take 4500 ++
        (coefficientPositiveTermChunk 1).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_064_a,
    coefficientEncodingLeafCheck_064_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_064
    coefficientSourceEncoding_064_a
    coefficientSourceEncoding_064_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
