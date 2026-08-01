
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part036A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part036B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf036.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_036 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf036.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_036 :
    coefficientCheckData (coefficientFactorTermChunk036) =
      (coefficientSourceEncoding_036,
        1099676042704960) := by
  rw [show coefficientFactorTermChunk036 =
      (coefficientFactorTermChunk036).take 2125 ++
        (coefficientFactorTermChunk036).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_036_a,
    coefficientEncodingLeafCheck_036_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_036
    coefficientSourceEncoding_036_a
    coefficientSourceEncoding_036_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
