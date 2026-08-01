


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf010.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_010 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf010.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_010 :
    coefficientCheckData (coefficientFactorTermChunk010) =
      (coefficientSourceEncoding_010,
        999672576411696) := by
  unfold coefficientCheckData coefficientSourceEncoding_010
  unfold coefficientFactorTermChunk010
    coefficientFactorTermRowData
    coefficientFullGramDataRow100
    coefficientFullGramDataRow101
    coefficientFullGramDataRow102
    coefficientFullGramDataRow103
    coefficientFullGramDataRow104
    coefficientFullGramDataRow105
    coefficientFullGramDataRow106
    coefficientFullGramDataRow107
    coefficientFullGramDataRow108
    coefficientFullGramDataRow109
    productIndexDataRow100
    productIndexDataRow101
    productIndexDataRow102
    productIndexDataRow103
    productIndexDataRow104
    productIndexDataRow105
    productIndexDataRow106
    productIndexDataRow107
    productIndexDataRow108
    productIndexDataRow109
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
