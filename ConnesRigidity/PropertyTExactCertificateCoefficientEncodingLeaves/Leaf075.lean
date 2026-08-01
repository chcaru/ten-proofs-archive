
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part075A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part075B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf075.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_075 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf075.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_075 :
    coefficientCheckData (coefficientPositiveTermChunk 12) =
      (coefficientSourceEncoding_075,
        30008546816) := by
  rw [show coefficientPositiveTermChunk 12 =
      (coefficientPositiveTermChunk 12).take 4500 ++
        (coefficientPositiveTermChunk 12).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_075_a,
    coefficientEncodingLeafCheck_075_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_075
    coefficientSourceEncoding_075_a
    coefficientSourceEncoding_075_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
