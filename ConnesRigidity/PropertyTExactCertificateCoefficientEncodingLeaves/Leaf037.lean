
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part037A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part037B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf037.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_037 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf037.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_037 :
    coefficientCheckData (coefficientFactorTermChunk037) =
      (coefficientSourceEncoding_037,
        1052762051860896) := by
  rw [show coefficientFactorTermChunk037 =
      (coefficientFactorTermChunk037).take 2125 ++
        (coefficientFactorTermChunk037).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_037_a,
    coefficientEncodingLeafCheck_037_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_037
    coefficientSourceEncoding_037_a
    coefficientSourceEncoding_037_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
