


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part065A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part065B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf065.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_065 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf065.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_065 :
    coefficientCheckData (coefficientPositiveTermChunk 2) =
      (coefficientSourceEncoding_065,
        39646030208) := by
  rw [show coefficientPositiveTermChunk 2 =
      (coefficientPositiveTermChunk 2).take 4500 ++
        (coefficientPositiveTermChunk 2).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_065_a,
    coefficientEncodingLeafCheck_065_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_065
    coefficientSourceEncoding_065_a
    coefficientSourceEncoding_065_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
