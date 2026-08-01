
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part038B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_038_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part038B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_038_b :
    coefficientCheckData ((coefficientFactorTermChunk038).drop 2125) =
      (coefficientSourceEncoding_038_b,
        494199493758240) := by
  unfold coefficientCheckData coefficientSourceEncoding_038_b
  unfold coefficientFactorTermChunk038
    coefficientFactorTermRowData
    coefficientFullGramDataRow380
    coefficientFullGramDataRow381
    coefficientFullGramDataRow382
    coefficientFullGramDataRow383
    coefficientFullGramDataRow384
    coefficientFullGramDataRow385
    coefficientFullGramDataRow386
    coefficientFullGramDataRow387
    coefficientFullGramDataRow388
    coefficientFullGramDataRow389
    productIndexDataRow380
    productIndexDataRow381
    productIndexDataRow382
    productIndexDataRow383
    productIndexDataRow384
    productIndexDataRow385
    productIndexDataRow386
    productIndexDataRow387
    productIndexDataRow388
    productIndexDataRow389
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
