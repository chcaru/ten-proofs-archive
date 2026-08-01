
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part035A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_035_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part035A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_035_a :
    coefficientCheckData ((coefficientFactorTermChunk035).take 2125) =
      (coefficientSourceEncoding_035_a,
        547211508846784) := by
  unfold coefficientCheckData coefficientSourceEncoding_035_a
  unfold coefficientFactorTermChunk035
    coefficientFactorTermRowData
    coefficientFullGramDataRow350
    coefficientFullGramDataRow351
    coefficientFullGramDataRow352
    coefficientFullGramDataRow353
    coefficientFullGramDataRow354
    coefficientFullGramDataRow355
    coefficientFullGramDataRow356
    coefficientFullGramDataRow357
    coefficientFullGramDataRow358
    coefficientFullGramDataRow359
    productIndexDataRow350
    productIndexDataRow351
    productIndexDataRow352
    productIndexDataRow353
    productIndexDataRow354
    productIndexDataRow355
    productIndexDataRow356
    productIndexDataRow357
    productIndexDataRow358
    productIndexDataRow359
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
