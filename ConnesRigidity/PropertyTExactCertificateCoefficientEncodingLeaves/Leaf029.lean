
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part029A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part029B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf029.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_029 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf029.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_029 :
    coefficientCheckData (coefficientFactorTermChunk029) =
      (coefficientSourceEncoding_029,
        672356944754176) := by
  rw [show coefficientFactorTermChunk029 =
      (coefficientFactorTermChunk029).take 2125 ++
        (coefficientFactorTermChunk029).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_029_a,
    coefficientEncodingLeafCheck_029_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_029
    coefficientSourceEncoding_029_a
    coefficientSourceEncoding_029_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
