


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part041A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_041_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part041A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_041_a :
    coefficientCheckData ((coefficientFactorTermChunk041).take 2125) =
      (coefficientSourceEncoding_041_a,
        514318779170544) := by
  unfold coefficientCheckData coefficientSourceEncoding_041_a
  unfold coefficientFactorTermChunk041
    coefficientFactorTermRowData
    coefficientFullGramDataRow410
    coefficientFullGramDataRow411
    coefficientFullGramDataRow412
    coefficientFullGramDataRow413
    coefficientFullGramDataRow414
    coefficientFullGramDataRow415
    coefficientFullGramDataRow416
    coefficientFullGramDataRow417
    coefficientFullGramDataRow418
    coefficientFullGramDataRow419
    productIndexDataRow410
    productIndexDataRow411
    productIndexDataRow412
    productIndexDataRow413
    productIndexDataRow414
    productIndexDataRow415
    productIndexDataRow416
    productIndexDataRow417
    productIndexDataRow418
    productIndexDataRow419
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
