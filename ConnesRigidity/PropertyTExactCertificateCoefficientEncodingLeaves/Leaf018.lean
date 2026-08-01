


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf018.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_018 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf018.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_018 :
    coefficientCheckData (coefficientFactorTermChunk018) =
      (coefficientSourceEncoding_018,
        617047743177600) := by
  unfold coefficientCheckData coefficientSourceEncoding_018
  unfold coefficientFactorTermChunk018
    coefficientFactorTermRowData
    coefficientFullGramDataRow180
    coefficientFullGramDataRow181
    coefficientFullGramDataRow182
    coefficientFullGramDataRow183
    coefficientFullGramDataRow184
    coefficientFullGramDataRow185
    coefficientFullGramDataRow186
    coefficientFullGramDataRow187
    coefficientFullGramDataRow188
    coefficientFullGramDataRow189
    productIndexDataRow180
    productIndexDataRow181
    productIndexDataRow182
    productIndexDataRow183
    productIndexDataRow184
    productIndexDataRow185
    productIndexDataRow186
    productIndexDataRow187
    productIndexDataRow188
    productIndexDataRow189
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
