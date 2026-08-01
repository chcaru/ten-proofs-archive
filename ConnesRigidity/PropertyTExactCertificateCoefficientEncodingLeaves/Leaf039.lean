
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part039A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part039B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf039.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_039 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf039.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_039 :
    coefficientCheckData (coefficientFactorTermChunk039) =
      (coefficientSourceEncoding_039,
        1040565932946000) := by
  rw [show coefficientFactorTermChunk039 =
      (coefficientFactorTermChunk039).take 2125 ++
        (coefficientFactorTermChunk039).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_039_a,
    coefficientEncodingLeafCheck_039_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_039
    coefficientSourceEncoding_039_a
    coefficientSourceEncoding_039_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
