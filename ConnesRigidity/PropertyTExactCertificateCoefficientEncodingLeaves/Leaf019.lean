


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf019.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_019 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf019.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_019 :
    coefficientCheckData (coefficientFactorTermChunk019) =
      (coefficientSourceEncoding_019,
        707976407897728) := by
  unfold coefficientCheckData coefficientSourceEncoding_019
  unfold coefficientFactorTermChunk019
    coefficientFactorTermRowData
    coefficientFullGramDataRow190
    coefficientFullGramDataRow191
    coefficientFullGramDataRow192
    coefficientFullGramDataRow193
    coefficientFullGramDataRow194
    coefficientFullGramDataRow195
    coefficientFullGramDataRow196
    coefficientFullGramDataRow197
    coefficientFullGramDataRow198
    coefficientFullGramDataRow199
    productIndexDataRow190
    productIndexDataRow191
    productIndexDataRow192
    productIndexDataRow193
    productIndexDataRow194
    productIndexDataRow195
    productIndexDataRow196
    productIndexDataRow197
    productIndexDataRow198
    productIndexDataRow199
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
