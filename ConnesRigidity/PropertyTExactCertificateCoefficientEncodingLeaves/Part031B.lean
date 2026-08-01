
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part031B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_031_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part031B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_031_b :
    coefficientCheckData ((coefficientFactorTermChunk031).drop 2125) =
      (coefficientSourceEncoding_031_b,
        401452285354208) := by
  unfold coefficientCheckData coefficientSourceEncoding_031_b
  unfold coefficientFactorTermChunk031
    coefficientFactorTermRowData
    coefficientFullGramDataRow310
    coefficientFullGramDataRow311
    coefficientFullGramDataRow312
    coefficientFullGramDataRow313
    coefficientFullGramDataRow314
    coefficientFullGramDataRow315
    coefficientFullGramDataRow316
    coefficientFullGramDataRow317
    coefficientFullGramDataRow318
    coefficientFullGramDataRow319
    productIndexDataRow310
    productIndexDataRow311
    productIndexDataRow312
    productIndexDataRow313
    productIndexDataRow314
    productIndexDataRow315
    productIndexDataRow316
    productIndexDataRow317
    productIndexDataRow318
    productIndexDataRow319
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
