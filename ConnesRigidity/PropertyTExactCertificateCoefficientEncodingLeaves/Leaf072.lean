
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part072A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part072B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf072.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_072 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf072.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_072 :
    coefficientCheckData (coefficientPositiveTermChunk 9) =
      (coefficientSourceEncoding_072,
        33780940800) := by
  rw [show coefficientPositiveTermChunk 9 =
      (coefficientPositiveTermChunk 9).take 4500 ++
        (coefficientPositiveTermChunk 9).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_072_a,
    coefficientEncodingLeafCheck_072_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_072
    coefficientSourceEncoding_072_a
    coefficientSourceEncoding_072_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
