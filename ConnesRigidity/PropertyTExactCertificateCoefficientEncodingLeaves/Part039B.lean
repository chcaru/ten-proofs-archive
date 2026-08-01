
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part039B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_039_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part039B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_039_b :
    coefficientCheckData ((coefficientFactorTermChunk039).drop 2125) =
      (coefficientSourceEncoding_039_b,
        449955579262336) := by
  unfold coefficientCheckData coefficientSourceEncoding_039_b
  unfold coefficientFactorTermChunk039
    coefficientFactorTermRowData
    coefficientFullGramDataRow390
    coefficientFullGramDataRow391
    coefficientFullGramDataRow392
    coefficientFullGramDataRow393
    coefficientFullGramDataRow394
    coefficientFullGramDataRow395
    coefficientFullGramDataRow396
    coefficientFullGramDataRow397
    coefficientFullGramDataRow398
    coefficientFullGramDataRow399
    productIndexDataRow390
    productIndexDataRow391
    productIndexDataRow392
    productIndexDataRow393
    productIndexDataRow394
    productIndexDataRow395
    productIndexDataRow396
    productIndexDataRow397
    productIndexDataRow398
    productIndexDataRow399
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
