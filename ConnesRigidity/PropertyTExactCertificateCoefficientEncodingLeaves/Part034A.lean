
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part034A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_034_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part034A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_034_a :
    coefficientCheckData ((coefficientFactorTermChunk034).take 2125) =
      (coefficientSourceEncoding_034_a,
        380971134765248) := by
  unfold coefficientCheckData coefficientSourceEncoding_034_a
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
