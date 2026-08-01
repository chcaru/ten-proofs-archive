
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part032A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part032B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf032.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_032 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf032.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_032 :
    coefficientCheckData (coefficientFactorTermChunk032) =
      (coefficientSourceEncoding_032,
        762717602847696) := by
  rw [show coefficientFactorTermChunk032 =
      (coefficientFactorTermChunk032).take 2125 ++
        (coefficientFactorTermChunk032).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_032_a,
    coefficientEncodingLeafCheck_032_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_032
    coefficientSourceEncoding_032_a
    coefficientSourceEncoding_032_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
