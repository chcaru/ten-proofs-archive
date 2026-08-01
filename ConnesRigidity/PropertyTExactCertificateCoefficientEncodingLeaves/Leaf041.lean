


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part041A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part041B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf041.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_041 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf041.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_041 :
    coefficientCheckData (coefficientFactorTermChunk041) =
      (coefficientSourceEncoding_041,
        993652050550976) := by
  rw [show coefficientFactorTermChunk041 =
      (coefficientFactorTermChunk041).take 2125 ++
        (coefficientFactorTermChunk041).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_041_a,
    coefficientEncodingLeafCheck_041_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_041
    coefficientSourceEncoding_041_a
    coefficientSourceEncoding_041_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
