
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf017.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_017 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf017.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_017 :
    coefficientCheckData (coefficientFactorTermChunk017) =
      (coefficientSourceEncoding_017,
        762717205149072) := by
  unfold coefficientCheckData coefficientSourceEncoding_017
  unfold coefficientFactorTermChunk017
    coefficientFactorTermRowData
    coefficientFullGramDataRow170
    coefficientFullGramDataRow171
    coefficientFullGramDataRow172
    coefficientFullGramDataRow173
    coefficientFullGramDataRow174
    coefficientFullGramDataRow175
    coefficientFullGramDataRow176
    coefficientFullGramDataRow177
    coefficientFullGramDataRow178
    coefficientFullGramDataRow179
    productIndexDataRow170
    productIndexDataRow171
    productIndexDataRow172
    productIndexDataRow173
    productIndexDataRow174
    productIndexDataRow175
    productIndexDataRow176
    productIndexDataRow177
    productIndexDataRow178
    productIndexDataRow179
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
