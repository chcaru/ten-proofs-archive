
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part066A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part066B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf066.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_066 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf066.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_066 :
    coefficientCheckData (coefficientPositiveTermChunk 3) =
      (coefficientSourceEncoding_066,
        36608248064) := by
  rw [show coefficientPositiveTermChunk 3 =
      (coefficientPositiveTermChunk 3).take 4500 ++
        (coefficientPositiveTermChunk 3).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_066_a,
    coefficientEncodingLeafCheck_066_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_066
    coefficientSourceEncoding_066_a
    coefficientSourceEncoding_066_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
