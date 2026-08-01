


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part038A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_038_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part038A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_038_a :
    coefficientCheckData ((coefficientFactorTermChunk038).take 2125) =
      (coefficientSourceEncoding_038_a,
        546366648004336) := by
  unfold coefficientCheckData coefficientSourceEncoding_038_a
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
