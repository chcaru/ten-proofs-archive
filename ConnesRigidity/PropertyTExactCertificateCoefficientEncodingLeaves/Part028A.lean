


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part028A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_028_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part028A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_028_a :
    coefficientCheckData ((coefficientFactorTermChunk028).take 2125) =
      (coefficientSourceEncoding_028_a,
        218403593876256) := by
  unfold coefficientCheckData coefficientSourceEncoding_028_a
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
