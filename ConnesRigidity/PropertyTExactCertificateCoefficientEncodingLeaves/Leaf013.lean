
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf013.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_013 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf013.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_013 :
    coefficientCheckData (coefficientFactorTermChunk013) =
      (coefficientSourceEncoding_013,
        806470620244336) := by
  unfold coefficientCheckData coefficientSourceEncoding_013
  unfold coefficientFactorTermChunk013
    coefficientFactorTermRowData
    coefficientFullGramDataRow130
    coefficientFullGramDataRow131
    coefficientFullGramDataRow132
    coefficientFullGramDataRow133
    coefficientFullGramDataRow134
    coefficientFullGramDataRow135
    coefficientFullGramDataRow136
    coefficientFullGramDataRow137
    coefficientFullGramDataRow138
    coefficientFullGramDataRow139
    productIndexDataRow130
    productIndexDataRow131
    productIndexDataRow132
    productIndexDataRow133
    productIndexDataRow134
    productIndexDataRow135
    productIndexDataRow136
    productIndexDataRow137
    productIndexDataRow138
    productIndexDataRow139
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
