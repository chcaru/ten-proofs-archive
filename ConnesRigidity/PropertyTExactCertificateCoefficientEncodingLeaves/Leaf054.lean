
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part054A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part054B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf054.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_054 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf054.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_054 :
    coefficientCheckData (coefficientNegativeTermChunk 11) =
      (coefficientSourceEncoding_054,
        8580690112) := by
  rw [show coefficientNegativeTermChunk 11 =
      (coefficientNegativeTermChunk 11).take 2000 ++
        (coefficientNegativeTermChunk 11).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_054_a,
    coefficientEncodingLeafCheck_054_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_054
    coefficientSourceEncoding_054_a
    coefficientSourceEncoding_054_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
