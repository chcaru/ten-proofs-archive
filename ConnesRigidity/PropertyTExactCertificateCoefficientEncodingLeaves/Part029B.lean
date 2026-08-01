


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part029B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_029_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part029B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_029_b :
    coefficientCheckData ((coefficientFactorTermChunk029).drop 2125) =
      (coefficientSourceEncoding_029_b,
        264282908889600) := by
  unfold coefficientCheckData coefficientSourceEncoding_029_b
  unfold coefficientFactorTermChunk029
    coefficientFactorTermRowData
    coefficientFullGramDataRow290
    coefficientFullGramDataRow291
    coefficientFullGramDataRow292
    coefficientFullGramDataRow293
    coefficientFullGramDataRow294
    coefficientFullGramDataRow295
    coefficientFullGramDataRow296
    coefficientFullGramDataRow297
    coefficientFullGramDataRow298
    coefficientFullGramDataRow299
    productIndexDataRow290
    productIndexDataRow291
    productIndexDataRow292
    productIndexDataRow293
    productIndexDataRow294
    productIndexDataRow295
    productIndexDataRow296
    productIndexDataRow297
    productIndexDataRow298
    productIndexDataRow299
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
