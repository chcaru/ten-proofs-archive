
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part063A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part063B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf063.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_063 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf063.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_063 :
    coefficientCheckData (coefficientPositiveTermChunk 0) =
      (coefficientSourceEncoding_063,
        118620576384) := by
  rw [show coefficientPositiveTermChunk 0 =
      (coefficientPositiveTermChunk 0).take 4018 ++
        (coefficientPositiveTermChunk 0).drop 4018 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_063_a,
    coefficientEncodingLeafCheck_063_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_063
    coefficientSourceEncoding_063_a
    coefficientSourceEncoding_063_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
