


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part073A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part073B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf073.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_073 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf073.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_073 :
    coefficientCheckData (coefficientPositiveTermChunk 10) =
      (coefficientSourceEncoding_073,
        37764607616) := by
  rw [show coefficientPositiveTermChunk 10 =
      (coefficientPositiveTermChunk 10).take 4500 ++
        (coefficientPositiveTermChunk 10).drop 4500 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_073_a,
    coefficientEncodingLeafCheck_073_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_073
    coefficientSourceEncoding_073_a
    coefficientSourceEncoding_073_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
