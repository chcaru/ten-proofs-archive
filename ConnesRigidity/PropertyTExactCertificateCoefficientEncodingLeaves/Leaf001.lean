


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf001.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_001 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf001.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_001 :
    coefficientCheckData (coefficientFactorTermChunk001) =
      (coefficientSourceEncoding_001,
        6194372700691792) := by
  unfold coefficientCheckData coefficientSourceEncoding_001
  unfold coefficientFactorTermChunk001
    coefficientFactorTermRowData
    coefficientFullGramDataRow010
    coefficientFullGramDataRow011
    coefficientFullGramDataRow012
    coefficientFullGramDataRow013
    coefficientFullGramDataRow014
    coefficientFullGramDataRow015
    coefficientFullGramDataRow016
    coefficientFullGramDataRow017
    coefficientFullGramDataRow018
    coefficientFullGramDataRow019
    productIndexDataRow010
    productIndexDataRow011
    productIndexDataRow012
    productIndexDataRow013
    productIndexDataRow014
    productIndexDataRow015
    productIndexDataRow016
    productIndexDataRow017
    productIndexDataRow018
    productIndexDataRow019
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
