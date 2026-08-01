
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part034B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_034_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part034B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_034_b :
    coefficientCheckData ((coefficientFactorTermChunk034).drop 2125) =
      (coefficientSourceEncoding_034_b,
        499452477669424) := by
  unfold coefficientCheckData coefficientSourceEncoding_034_b
  unfold coefficientFactorTermChunk034
    coefficientFactorTermRowData
    coefficientFullGramDataRow340
    coefficientFullGramDataRow341
    coefficientFullGramDataRow342
    coefficientFullGramDataRow343
    coefficientFullGramDataRow344
    coefficientFullGramDataRow345
    coefficientFullGramDataRow346
    coefficientFullGramDataRow347
    coefficientFullGramDataRow348
    coefficientFullGramDataRow349
    productIndexDataRow340
    productIndexDataRow341
    productIndexDataRow342
    productIndexDataRow343
    productIndexDataRow344
    productIndexDataRow345
    productIndexDataRow346
    productIndexDataRow347
    productIndexDataRow348
    productIndexDataRow349
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
