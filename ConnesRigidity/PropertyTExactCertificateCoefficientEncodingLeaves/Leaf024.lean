


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf024.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_024 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf024.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_024 :
    coefficientCheckData (coefficientFactorTermChunk024) =
      (coefficientSourceEncoding_024,
        872395640842736) := by
  unfold coefficientCheckData coefficientSourceEncoding_024
  unfold coefficientFactorTermChunk024
    coefficientFactorTermRowData
    coefficientFullGramDataRow240
    coefficientFullGramDataRow241
    coefficientFullGramDataRow242
    coefficientFullGramDataRow243
    coefficientFullGramDataRow244
    coefficientFullGramDataRow245
    coefficientFullGramDataRow246
    coefficientFullGramDataRow247
    coefficientFullGramDataRow248
    coefficientFullGramDataRow249
    productIndexDataRow240
    productIndexDataRow241
    productIndexDataRow242
    productIndexDataRow243
    productIndexDataRow244
    productIndexDataRow245
    productIndexDataRow246
    productIndexDataRow247
    productIndexDataRow248
    productIndexDataRow249
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
