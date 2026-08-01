


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part030A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part030B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf030.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_030 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf030.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_030 :
    coefficientCheckData (coefficientFactorTermChunk030) =
      (coefficientSourceEncoding_030,
        1028554211998400) := by
  rw [show coefficientFactorTermChunk030 =
      (coefficientFactorTermChunk030).take 2125 ++
        (coefficientFactorTermChunk030).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_030_a,
    coefficientEncodingLeafCheck_030_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_030
    coefficientSourceEncoding_030_a
    coefficientSourceEncoding_030_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
