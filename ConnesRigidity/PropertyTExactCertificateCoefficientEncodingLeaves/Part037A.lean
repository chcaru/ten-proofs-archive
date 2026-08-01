
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part037A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_037_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part037A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_037_a :
    coefficientCheckData ((coefficientFactorTermChunk037).take 2125) =
      (coefficientSourceEncoding_037_a,
        514318852280304) := by
  unfold coefficientCheckData coefficientSourceEncoding_037_a
  unfold coefficientFactorTermChunk037
    coefficientFactorTermRowData
    coefficientFullGramDataRow370
    coefficientFullGramDataRow371
    coefficientFullGramDataRow372
    coefficientFullGramDataRow373
    coefficientFullGramDataRow374
    coefficientFullGramDataRow375
    coefficientFullGramDataRow376
    coefficientFullGramDataRow377
    coefficientFullGramDataRow378
    coefficientFullGramDataRow379
    productIndexDataRow370
    productIndexDataRow371
    productIndexDataRow372
    productIndexDataRow373
    productIndexDataRow374
    productIndexDataRow375
    productIndexDataRow376
    productIndexDataRow377
    productIndexDataRow378
    productIndexDataRow379
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
