


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part042B.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_042_b :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Part042B.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_042_b :
    coefficientCheckData ((coefficientFactorTermChunk042).drop 1062) =
      (coefficientSourceEncoding_042_b,
        212816871761976) := by
  unfold coefficientCheckData coefficientSourceEncoding_042_b
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
