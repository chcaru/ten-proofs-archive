
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part028A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part028B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf028.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_028 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf028.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_028 :
    coefficientCheckData (coefficientFactorTermChunk028) =
      (coefficientSourceEncoding_028,
        599374621226416) := by
  rw [show coefficientFactorTermChunk028 =
      (coefficientFactorTermChunk028).take 2125 ++
        (coefficientFactorTermChunk028).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_028_a,
    coefficientEncodingLeafCheck_028_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_028
    coefficientSourceEncoding_028_a
    coefficientSourceEncoding_028_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
