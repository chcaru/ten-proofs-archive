
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part078A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part078B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf078.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_078 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf078.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_078 :
    coefficientCheckData (coefficientPositiveTermChunk 15) =
      (coefficientSourceEncoding_078,
        33592402816) := by
  rw [show coefficientPositiveTermChunk 15 =
      (coefficientPositiveTermChunk 15).take 4500 ++
        (coefficientPositiveTermChunk 15).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_078_a,
    coefficientEncodingLeafCheck_078_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_078
    coefficientSourceEncoding_078_a
    coefficientSourceEncoding_078_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
