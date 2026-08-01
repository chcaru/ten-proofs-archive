
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part069A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part069B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf069.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_069 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf069.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_069 :
    coefficientCheckData (coefficientPositiveTermChunk 6) =
      (coefficientSourceEncoding_069,
        41505819776) := by
  rw [show coefficientPositiveTermChunk 6 =
      (coefficientPositiveTermChunk 6).take 4500 ++
        (coefficientPositiveTermChunk 6).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_069_a,
    coefficientEncodingLeafCheck_069_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_069
    coefficientSourceEncoding_069_a
    coefficientSourceEncoding_069_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
