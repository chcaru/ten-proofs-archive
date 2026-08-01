
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part033B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_033_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part033B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_033_b :
    coefficientCheckData ((coefficientFactorTermChunk033).drop 2125) =
      (coefficientSourceEncoding_033_b,
        337849878142448) := by
  unfold coefficientCheckData coefficientSourceEncoding_033_b
  unfold coefficientFactorTermChunk033
    coefficientFactorTermRowData
    coefficientFullGramDataRow330
    coefficientFullGramDataRow331
    coefficientFullGramDataRow332
    coefficientFullGramDataRow333
    coefficientFullGramDataRow334
    coefficientFullGramDataRow335
    coefficientFullGramDataRow336
    coefficientFullGramDataRow337
    coefficientFullGramDataRow338
    coefficientFullGramDataRow339
    productIndexDataRow330
    productIndexDataRow331
    productIndexDataRow332
    productIndexDataRow333
    productIndexDataRow334
    productIndexDataRow335
    productIndexDataRow336
    productIndexDataRow337
    productIndexDataRow338
    productIndexDataRow339
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
