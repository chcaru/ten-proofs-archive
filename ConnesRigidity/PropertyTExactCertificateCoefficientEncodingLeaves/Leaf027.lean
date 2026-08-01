


import ConnesRigidity.PropertyTExactCertificateCoefficientAppend
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part027A
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingLeaves.Part027B
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf027.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_027 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf027.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_027 :
    coefficientCheckData (coefficientFactorTermChunk027) =
      (coefficientSourceEncoding_027,
        703451401970624) := by
  rw [show coefficientFactorTermChunk027 =
      (coefficientFactorTermChunk027).take 2125 ++
        (coefficientFactorTermChunk027).drop 2125 by
    exact (List.take_append_drop _ _).symm]
  rw [coefficientCheckData_append,
    coefficientEncodingLeafCheck_027_a,
    coefficientEncodingLeafCheck_027_b]
  unfold addCoefficientEncodingRows
    coefficientSourceEncoding_027
    coefficientSourceEncoding_027_a
    coefficientSourceEncoding_027_b
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
