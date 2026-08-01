
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part040A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part040B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf040.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_040 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf040.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_040 :
    coefficientCheckData (coefficientFactorTermChunk040) =
      (coefficientSourceEncoding_040,
        1052761860824848) := by
  rw [show coefficientFactorTermChunk040 =
      (coefficientFactorTermChunk040).take 2125 ++
        (coefficientFactorTermChunk040).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_040_a,
    coefficientEncodingLeafCheck_040_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_040
    coefficientSourceEncoding_040_a
    coefficientSourceEncoding_040_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
