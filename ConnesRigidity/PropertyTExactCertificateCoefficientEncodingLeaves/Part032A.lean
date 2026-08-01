
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part032A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_032_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part032A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_032_a :
    coefficientCheckData ((coefficientFactorTermChunk032).take 2125) =
      (coefficientSourceEncoding_032_a,
        476746924320752) := by
  unfold coefficientCheckData coefficientSourceEncoding_032_a
  unfold coefficientFactorTermChunk032
    coefficientFactorTermRowData
    coefficientFullGramDataRow320
    coefficientFullGramDataRow321
    coefficientFullGramDataRow322
    coefficientFullGramDataRow323
    coefficientFullGramDataRow324
    coefficientFullGramDataRow325
    coefficientFullGramDataRow326
    coefficientFullGramDataRow327
    coefficientFullGramDataRow328
    coefficientFullGramDataRow329
    productIndexDataRow320
    productIndexDataRow321
    productIndexDataRow322
    productIndexDataRow323
    productIndexDataRow324
    productIndexDataRow325
    productIndexDataRow326
    productIndexDataRow327
    productIndexDataRow328
    productIndexDataRow329
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
