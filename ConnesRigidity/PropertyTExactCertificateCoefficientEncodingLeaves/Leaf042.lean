


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part042A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part042B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf042.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_042 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf042.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_042 :
    coefficientCheckData (coefficientFactorTermChunk042) =
      (coefficientSourceEncoding_042,
        449955631071808) := by
  rw [show coefficientFactorTermChunk042 =
      (coefficientFactorTermChunk042).take 1062 ++
        (coefficientFactorTermChunk042).drop 1062 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_042_a,
    coefficientEncodingLeafCheck_042_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_042
    coefficientSourceEncoding_042_a
    coefficientSourceEncoding_042_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
