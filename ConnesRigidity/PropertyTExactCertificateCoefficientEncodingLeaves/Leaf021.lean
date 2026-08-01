


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf021.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_021 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf021.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_021 :
    coefficientCheckData (coefficientFactorTermChunk021) =
      (coefficientSourceEncoding_021,
        739263322835424) := by
  unfold coefficientCheckData coefficientSourceEncoding_021
  unfold coefficientFactorTermChunk021
    coefficientFactorTermRowData
    coefficientFullGramDataRow210
    coefficientFullGramDataRow211
    coefficientFullGramDataRow212
    coefficientFullGramDataRow213
    coefficientFullGramDataRow214
    coefficientFullGramDataRow215
    coefficientFullGramDataRow216
    coefficientFullGramDataRow217
    coefficientFullGramDataRow218
    coefficientFullGramDataRow219
    productIndexDataRow210
    productIndexDataRow211
    productIndexDataRow212
    productIndexDataRow213
    productIndexDataRow214
    productIndexDataRow215
    productIndexDataRow216
    productIndexDataRow217
    productIndexDataRow218
    productIndexDataRow219
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
