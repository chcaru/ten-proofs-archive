
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part026B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_026_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part026B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_026_b :
    coefficientCheckData ((coefficientFactorTermChunk026).drop 2125) =
      (coefficientSourceEncoding_026_b,
        417022920487648) := by
  unfold coefficientCheckData coefficientSourceEncoding_026_b
  unfold coefficientFactorTermChunk026
    coefficientFactorTermRowData
    coefficientFullGramDataRow260
    coefficientFullGramDataRow261
    coefficientFullGramDataRow262
    coefficientFullGramDataRow263
    coefficientFullGramDataRow264
    coefficientFullGramDataRow265
    coefficientFullGramDataRow266
    coefficientFullGramDataRow267
    coefficientFullGramDataRow268
    coefficientFullGramDataRow269
    productIndexDataRow260
    productIndexDataRow261
    productIndexDataRow262
    productIndexDataRow263
    productIndexDataRow264
    productIndexDataRow265
    productIndexDataRow266
    productIndexDataRow267
    productIndexDataRow268
    productIndexDataRow269
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
