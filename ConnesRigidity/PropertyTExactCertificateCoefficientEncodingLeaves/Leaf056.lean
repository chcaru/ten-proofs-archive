
import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part056A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part056B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf056.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_056 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf056.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_056 :
    coefficientCheckData (coefficientNegativeTermChunk 13) =
      (coefficientSourceEncoding_056,
        9124885472) := by
  rw [show coefficientNegativeTermChunk 13 =
      (coefficientNegativeTermChunk 13).take 2000 ++
        (coefficientNegativeTermChunk 13).drop 2000 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_056_a,
    coefficientEncodingLeafCheck_056_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_056
    coefficientSourceEncoding_056_a
    coefficientSourceEncoding_056_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
