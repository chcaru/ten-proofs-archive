
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part030B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_030_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part030B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_030_b :
    coefficientCheckData ((coefficientFactorTermChunk030).drop 2125) =
      (coefficientSourceEncoding_030_b,
        458082850040800) := by
  unfold coefficientCheckData coefficientSourceEncoding_030_b
  unfold coefficientFactorTermChunk030
    coefficientFactorTermRowData
    coefficientFullGramDataRow300
    coefficientFullGramDataRow301
    coefficientFullGramDataRow302
    coefficientFullGramDataRow303
    coefficientFullGramDataRow304
    coefficientFullGramDataRow305
    coefficientFullGramDataRow306
    coefficientFullGramDataRow307
    coefficientFullGramDataRow308
    coefficientFullGramDataRow309
    productIndexDataRow300
    productIndexDataRow301
    productIndexDataRow302
    productIndexDataRow303
    productIndexDataRow304
    productIndexDataRow305
    productIndexDataRow306
    productIndexDataRow307
    productIndexDataRow308
    productIndexDataRow309
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
