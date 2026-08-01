


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf020.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_020 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf020.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_020 :
    coefficientCheckData (coefficientFactorTermChunk020) =
      (coefficientSourceEncoding_020,
        582365792024144) := by
  unfold coefficientCheckData coefficientSourceEncoding_020
  unfold coefficientFactorTermChunk020
    coefficientFactorTermRowData
    coefficientFullGramDataRow200
    coefficientFullGramDataRow201
    coefficientFullGramDataRow202
    coefficientFullGramDataRow203
    coefficientFullGramDataRow204
    coefficientFullGramDataRow205
    coefficientFullGramDataRow206
    coefficientFullGramDataRow207
    coefficientFullGramDataRow208
    coefficientFullGramDataRow209
    productIndexDataRow200
    productIndexDataRow201
    productIndexDataRow202
    productIndexDataRow203
    productIndexDataRow204
    productIndexDataRow205
    productIndexDataRow206
    productIndexDataRow207
    productIndexDataRow208
    productIndexDataRow209
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
