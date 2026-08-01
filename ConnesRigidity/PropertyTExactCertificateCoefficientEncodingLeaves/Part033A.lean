


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part033A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_033_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part033A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_033_a :
    coefficientCheckData ((coefficientFactorTermChunk033).take 2125) =
      (coefficientSourceEncoding_033_a,
        251638904054176) := by
  unfold coefficientCheckData coefficientSourceEncoding_033_a
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
