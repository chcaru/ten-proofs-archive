
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part031A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part031B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf031.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_031 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf031.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_031 :
    coefficientCheckData (coefficientFactorTermChunk031) =
      (coefficientSourceEncoding_031,
        704624753223408) := by
  rw [show coefficientFactorTermChunk031 =
      (coefficientFactorTermChunk031).take 2125 ++
        (coefficientFactorTermChunk031).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_031_a,
    coefficientEncodingLeafCheck_031_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_031
    coefficientSourceEncoding_031_a
    coefficientSourceEncoding_031_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
