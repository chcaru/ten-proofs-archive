


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part036B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_036_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part036B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_036_b :
    coefficientCheckData ((coefficientFactorTermChunk036).drop 2125) =
      (coefficientSourceEncoding_036_b,
        649720353199952) := by
  unfold coefficientCheckData coefficientSourceEncoding_036_b
  unfold coefficientFactorTermChunk036
    coefficientFactorTermRowData
    coefficientFullGramDataRow360
    coefficientFullGramDataRow361
    coefficientFullGramDataRow362
    coefficientFullGramDataRow363
    coefficientFullGramDataRow364
    coefficientFullGramDataRow365
    coefficientFullGramDataRow366
    coefficientFullGramDataRow367
    coefficientFullGramDataRow368
    coefficientFullGramDataRow369
    productIndexDataRow360
    productIndexDataRow361
    productIndexDataRow362
    productIndexDataRow363
    productIndexDataRow364
    productIndexDataRow365
    productIndexDataRow366
    productIndexDataRow367
    productIndexDataRow368
    productIndexDataRow369
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
