
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part026A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part026B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf026.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_026 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf026.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_026 :
    coefficientCheckData (coefficientFactorTermChunk026) =
      (coefficientSourceEncoding_026,
        836676906310480) := by
  rw [show coefficientFactorTermChunk026 =
      (coefficientFactorTermChunk026).take 2125 ++
        (coefficientFactorTermChunk026).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_026_a,
    coefficientEncodingLeafCheck_026_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_026
    coefficientSourceEncoding_026_a
    coefficientSourceEncoding_026_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
