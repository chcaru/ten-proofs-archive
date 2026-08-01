


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part033A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part033B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf033.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_033 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf033.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_033 :
    coefficientCheckData (coefficientFactorTermChunk033) =
      (coefficientSourceEncoding_033,
        589488782196624) := by
  rw [show coefficientFactorTermChunk033 =
      (coefficientFactorTermChunk033).take 2125 ++
        (coefficientFactorTermChunk033).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_033_a,
    coefficientEncodingLeafCheck_033_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_033
    coefficientSourceEncoding_033_a
    coefficientSourceEncoding_033_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
