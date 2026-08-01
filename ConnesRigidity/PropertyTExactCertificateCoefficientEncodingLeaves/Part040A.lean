


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part040A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_040_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part040A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_040_a :
    coefficientCheckData ((coefficientFactorTermChunk040).take 2125) =
      (coefficientSourceEncoding_040_a,
        558562452358560) := by
  unfold coefficientCheckData coefficientSourceEncoding_040_a
  unfold coefficientFactorTermChunk040
    coefficientFactorTermRowData
    coefficientFullGramDataRow400
    coefficientFullGramDataRow401
    coefficientFullGramDataRow402
    coefficientFullGramDataRow403
    coefficientFullGramDataRow404
    coefficientFullGramDataRow405
    coefficientFullGramDataRow406
    coefficientFullGramDataRow407
    coefficientFullGramDataRow408
    coefficientFullGramDataRow409
    productIndexDataRow400
    productIndexDataRow401
    productIndexDataRow402
    productIndexDataRow403
    productIndexDataRow404
    productIndexDataRow405
    productIndexDataRow406
    productIndexDataRow407
    productIndexDataRow408
    productIndexDataRow409
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
