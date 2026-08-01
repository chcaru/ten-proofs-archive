
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part068A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part068B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf068.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_068 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf068.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_068 :
    coefficientCheckData (coefficientPositiveTermChunk 5) =
      (coefficientSourceEncoding_068,
        39853191296) := by
  rw [show coefficientPositiveTermChunk 5 =
      (coefficientPositiveTermChunk 5).take 4500 ++
        (coefficientPositiveTermChunk 5).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_068_a,
    coefficientEncodingLeafCheck_068_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_068
    coefficientSourceEncoding_068_a
    coefficientSourceEncoding_068_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
