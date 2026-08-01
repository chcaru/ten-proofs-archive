
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part026A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_026_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part026A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_026_a :
    coefficientCheckData ((coefficientFactorTermChunk026).take 2125) =
      (coefficientSourceEncoding_026_a,
        419653985822832) := by
  unfold coefficientCheckData coefficientSourceEncoding_026_a
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
