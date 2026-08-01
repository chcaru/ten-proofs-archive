
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part036A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_036_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part036A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_036_a :
    coefficientCheckData ((coefficientFactorTermChunk036).take 2125) =
      (coefficientSourceEncoding_036_a,
        449955689505008) := by
  unfold coefficientCheckData coefficientSourceEncoding_036_a
  unfold coefficientFactorTermChunk036
    coefficientFactorTermRowData
    coefficientFullGramDataRow360
    coefficientFullGramDataRow361
    coefficientFullGramDataRow362
    coefficientFullGramDataRow363
    coefficientFullGramDataRow364
    coefficientFullGramDataRow365
    coefficientFullGramDataRow366
    coefficientFullGramDataRow367
    coefficientFullGramDataRow368
    coefficientFullGramDataRow369
    productIndexDataRow360
    productIndexDataRow361
    productIndexDataRow362
    productIndexDataRow363
    productIndexDataRow364
    productIndexDataRow365
    productIndexDataRow366
    productIndexDataRow367
    productIndexDataRow368
    productIndexDataRow369
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
