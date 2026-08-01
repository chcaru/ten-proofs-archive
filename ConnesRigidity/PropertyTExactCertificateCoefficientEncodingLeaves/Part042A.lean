


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part042A.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_042_a :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part042A.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_042_a :
    coefficientCheckData ((coefficientFactorTermChunk042).take 1062) =
      (coefficientSourceEncoding_042_a,
        237138759309832) := by
  unfold coefficientCheckData coefficientSourceEncoding_042_a
  unfold coefficientFactorTermChunk042
    coefficientFactorTermRowData
    coefficientFullGramDataRow420
    coefficientFullGramDataRow421
    coefficientFullGramDataRow422
    coefficientFullGramDataRow423
    coefficientFullGramDataRow424
    productIndexDataRow420
    productIndexDataRow421
    productIndexDataRow422
    productIndexDataRow423
    productIndexDataRow424
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
