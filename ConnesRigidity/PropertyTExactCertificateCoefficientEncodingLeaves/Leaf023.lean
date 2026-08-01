


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf023.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_023 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf023.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_023 :
    coefficientCheckData (coefficientFactorTermChunk023) =
      (coefficientSourceEncoding_023,
        760924807130576) := by
  unfold coefficientCheckData coefficientSourceEncoding_023
  unfold coefficientFactorTermChunk023
    coefficientFactorTermRowData
    coefficientFullGramDataRow230
    coefficientFullGramDataRow231
    coefficientFullGramDataRow232
    coefficientFullGramDataRow233
    coefficientFullGramDataRow234
    coefficientFullGramDataRow235
    coefficientFullGramDataRow236
    coefficientFullGramDataRow237
    coefficientFullGramDataRow238
    coefficientFullGramDataRow239
    productIndexDataRow230
    productIndexDataRow231
    productIndexDataRow232
    productIndexDataRow233
    productIndexDataRow234
    productIndexDataRow235
    productIndexDataRow236
    productIndexDataRow237
    productIndexDataRow238
    productIndexDataRow239
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
