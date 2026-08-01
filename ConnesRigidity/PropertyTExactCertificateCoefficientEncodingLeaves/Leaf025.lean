


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf025.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_025 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf025.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_025 :
    coefficientCheckData (coefficientFactorTermChunk025) =
      (coefficientSourceEncoding_025,
        871492586692112) := by
  unfold coefficientCheckData coefficientSourceEncoding_025
  unfold coefficientFactorTermChunk025
    coefficientFactorTermRowData
    coefficientFullGramDataRow250
    coefficientFullGramDataRow251
    coefficientFullGramDataRow252
    coefficientFullGramDataRow253
    coefficientFullGramDataRow254
    coefficientFullGramDataRow255
    coefficientFullGramDataRow256
    coefficientFullGramDataRow257
    coefficientFullGramDataRow258
    coefficientFullGramDataRow259
    productIndexDataRow250
    productIndexDataRow251
    productIndexDataRow252
    productIndexDataRow253
    productIndexDataRow254
    productIndexDataRow255
    productIndexDataRow256
    productIndexDataRow257
    productIndexDataRow258
    productIndexDataRow259
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
