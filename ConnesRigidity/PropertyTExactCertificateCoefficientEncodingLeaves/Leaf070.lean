
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part070A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part070B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf070.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_070 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf070.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_070 :
    coefficientCheckData (coefficientPositiveTermChunk 7) =
      (coefficientSourceEncoding_070,
        39442781568) := by
  rw [show coefficientPositiveTermChunk 7 =
      (coefficientPositiveTermChunk 7).take 4500 ++
        (coefficientPositiveTermChunk 7).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_070_a,
    coefficientEncodingLeafCheck_070_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_070
    coefficientSourceEncoding_070_a
    coefficientSourceEncoding_070_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
