


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf022.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_022 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf022.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_022 :
    coefficientCheckData (coefficientFactorTermChunk022) =
      (coefficientSourceEncoding_022,
        582365588486640) := by
  unfold coefficientCheckData coefficientSourceEncoding_022
  unfold coefficientFactorTermChunk022
    coefficientFactorTermRowData
    coefficientFullGramDataRow220
    coefficientFullGramDataRow221
    coefficientFullGramDataRow222
    coefficientFullGramDataRow223
    coefficientFullGramDataRow224
    coefficientFullGramDataRow225
    coefficientFullGramDataRow226
    coefficientFullGramDataRow227
    coefficientFullGramDataRow228
    coefficientFullGramDataRow229
    productIndexDataRow220
    productIndexDataRow221
    productIndexDataRow222
    productIndexDataRow223
    productIndexDataRow224
    productIndexDataRow225
    productIndexDataRow226
    productIndexDataRow227
    productIndexDataRow228
    productIndexDataRow229
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
