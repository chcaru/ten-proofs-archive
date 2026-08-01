
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part027A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_027_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part027A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_027_a :
    coefficientCheckData ((coefficientFactorTermChunk027).take 2125) =
      (coefficientSourceEncoding_027_a,
        451812516450384) := by
  unfold coefficientCheckData coefficientSourceEncoding_027_a
  unfold coefficientFactorTermChunk027
    coefficientFactorTermRowData
    coefficientFullGramDataRow270
    coefficientFullGramDataRow271
    coefficientFullGramDataRow272
    coefficientFullGramDataRow273
    coefficientFullGramDataRow274
    coefficientFullGramDataRow275
    coefficientFullGramDataRow276
    coefficientFullGramDataRow277
    coefficientFullGramDataRow278
    coefficientFullGramDataRow279
    productIndexDataRow270
    productIndexDataRow271
    productIndexDataRow272
    productIndexDataRow273
    productIndexDataRow274
    productIndexDataRow275
    productIndexDataRow276
    productIndexDataRow277
    productIndexDataRow278
    productIndexDataRow279
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
