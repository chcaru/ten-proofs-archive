


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part074A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part074B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf074.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_074 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf074.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_074 :
    coefficientCheckData (coefficientPositiveTermChunk 11) =
      (coefficientSourceEncoding_074,
        37729499520) := by
  rw [show coefficientPositiveTermChunk 11 =
      (coefficientPositiveTermChunk 11).take 4500 ++
        (coefficientPositiveTermChunk 11).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_074_a,
    coefficientEncodingLeafCheck_074_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_074
    coefficientSourceEncoding_074_a
    coefficientSourceEncoding_074_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
