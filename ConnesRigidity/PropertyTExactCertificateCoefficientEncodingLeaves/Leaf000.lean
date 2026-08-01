


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf000.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_000 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf000.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_000 :
    coefficientCheckData (coefficientFactorTermChunk000) =
      (coefficientSourceEncoding_000,
        11111025030390144) := by
  unfold coefficientCheckData coefficientSourceEncoding_000
  unfold coefficientFactorTermChunk000
    coefficientFactorTermRowData
    coefficientFullGramDataRow000
    coefficientFullGramDataRow001
    coefficientFullGramDataRow002
    coefficientFullGramDataRow003
    coefficientFullGramDataRow004
    coefficientFullGramDataRow005
    coefficientFullGramDataRow006
    coefficientFullGramDataRow007
    coefficientFullGramDataRow008
    coefficientFullGramDataRow009
    productIndexDataRow000
    productIndexDataRow001
    productIndexDataRow002
    productIndexDataRow003
    productIndexDataRow004
    productIndexDataRow005
    productIndexDataRow006
    productIndexDataRow007
    productIndexDataRow008
    productIndexDataRow009
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
