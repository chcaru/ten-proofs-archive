


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf016.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_016 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf016.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_016 :
    coefficientCheckData (coefficientFactorTermChunk016) =
      (coefficientSourceEncoding_016,
        1039937126510368) := by
  unfold coefficientCheckData coefficientSourceEncoding_016
  unfold coefficientFactorTermChunk016
    coefficientFactorTermRowData
    coefficientFullGramDataRow160
    coefficientFullGramDataRow161
    coefficientFullGramDataRow162
    coefficientFullGramDataRow163
    coefficientFullGramDataRow164
    coefficientFullGramDataRow165
    coefficientFullGramDataRow166
    coefficientFullGramDataRow167
    coefficientFullGramDataRow168
    coefficientFullGramDataRow169
    productIndexDataRow160
    productIndexDataRow161
    productIndexDataRow162
    productIndexDataRow163
    productIndexDataRow164
    productIndexDataRow165
    productIndexDataRow166
    productIndexDataRow167
    productIndexDataRow168
    productIndexDataRow169
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
