


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf015.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_015 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf015.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_015 :
    coefficientCheckData (coefficientFactorTermChunk015) =
      (coefficientSourceEncoding_015,
        763425895699088) := by
  unfold coefficientCheckData coefficientSourceEncoding_015
  unfold coefficientFactorTermChunk015
    coefficientFactorTermRowData
    coefficientFullGramDataRow150
    coefficientFullGramDataRow151
    coefficientFullGramDataRow152
    coefficientFullGramDataRow153
    coefficientFullGramDataRow154
    coefficientFullGramDataRow155
    coefficientFullGramDataRow156
    coefficientFullGramDataRow157
    coefficientFullGramDataRow158
    coefficientFullGramDataRow159
    productIndexDataRow150
    productIndexDataRow151
    productIndexDataRow152
    productIndexDataRow153
    productIndexDataRow154
    productIndexDataRow155
    productIndexDataRow156
    productIndexDataRow157
    productIndexDataRow158
    productIndexDataRow159
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
