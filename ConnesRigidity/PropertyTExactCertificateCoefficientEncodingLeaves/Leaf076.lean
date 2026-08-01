


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part076A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part076B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf076.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_076 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf076.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_076 :
    coefficientCheckData (coefficientPositiveTermChunk 13) =
      (coefficientSourceEncoding_076,
        31592744704) := by
  rw [show coefficientPositiveTermChunk 13 =
      (coefficientPositiveTermChunk 13).take 4500 ++
        (coefficientPositiveTermChunk 13).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_076_a,
    coefficientEncodingLeafCheck_076_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_076
    coefficientSourceEncoding_076_a
    coefficientSourceEncoding_076_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
