
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part067A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part067B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf067.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_067 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf067.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_067 :
    coefficientCheckData (coefficientPositiveTermChunk 4) =
      (coefficientSourceEncoding_067,
        37749601920) := by
  rw [show coefficientPositiveTermChunk 4 =
      (coefficientPositiveTermChunk 4).take 4500 ++
        (coefficientPositiveTermChunk 4).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_067_a,
    coefficientEncodingLeafCheck_067_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_067
    coefficientSourceEncoding_067_a
    coefficientSourceEncoding_067_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
