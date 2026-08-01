


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part035A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part035B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf035.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_035 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf035.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_035 :
    coefficientCheckData (coefficientFactorTermChunk035) =
      (coefficientSourceEncoding_035,
        1143919686161760) := by
  rw [show coefficientFactorTermChunk035 =
      (coefficientFactorTermChunk035).take 2125 ++
        (coefficientFactorTermChunk035).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_035_a,
    coefficientEncodingLeafCheck_035_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_035
    coefficientSourceEncoding_035_a
    coefficientSourceEncoding_035_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
