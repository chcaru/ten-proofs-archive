


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part028B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_028_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part028B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_028_b :
    coefficientCheckData ((coefficientFactorTermChunk028).drop 2125) =
      (coefficientSourceEncoding_028_b,
        380971027350160) := by
  unfold coefficientCheckData coefficientSourceEncoding_028_b
  unfold coefficientFactorTermChunk028
    coefficientFactorTermRowData
    coefficientFullGramDataRow280
    coefficientFullGramDataRow281
    coefficientFullGramDataRow282
    coefficientFullGramDataRow283
    coefficientFullGramDataRow284
    coefficientFullGramDataRow285
    coefficientFullGramDataRow286
    coefficientFullGramDataRow287
    coefficientFullGramDataRow288
    coefficientFullGramDataRow289
    productIndexDataRow280
    productIndexDataRow281
    productIndexDataRow282
    productIndexDataRow283
    productIndexDataRow284
    productIndexDataRow285
    productIndexDataRow286
    productIndexDataRow287
    productIndexDataRow288
    productIndexDataRow289
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
