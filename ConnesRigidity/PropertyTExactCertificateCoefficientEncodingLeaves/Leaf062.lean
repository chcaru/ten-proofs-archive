


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part062A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part062B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf062.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_062 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf062.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_062 :
    coefficientCheckData (coefficientNegativeTermChunk 19) =
      (coefficientSourceEncoding_062,
        3342913504) := by
  rw [show coefficientNegativeTermChunk 19 =
      (coefficientNegativeTermChunk 19).take 746 ++
        (coefficientNegativeTermChunk 19).drop 746 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_062_a,
    coefficientEncodingLeafCheck_062_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_062
    coefficientSourceEncoding_062_a
    coefficientSourceEncoding_062_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
