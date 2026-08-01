
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf011.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_011 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf011.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_011 :
    coefficientCheckData (coefficientFactorTermChunk011) =
      (coefficientSourceEncoding_011,
        670216167706816) := by
  unfold coefficientCheckData coefficientSourceEncoding_011
  unfold coefficientFactorTermChunk011
    coefficientFactorTermRowData
    coefficientFullGramDataRow110
    coefficientFullGramDataRow111
    coefficientFullGramDataRow112
    coefficientFullGramDataRow113
    coefficientFullGramDataRow114
    coefficientFullGramDataRow115
    coefficientFullGramDataRow116
    coefficientFullGramDataRow117
    coefficientFullGramDataRow118
    coefficientFullGramDataRow119
    productIndexDataRow110
    productIndexDataRow111
    productIndexDataRow112
    productIndexDataRow113
    productIndexDataRow114
    productIndexDataRow115
    productIndexDataRow116
    productIndexDataRow117
    productIndexDataRow118
    productIndexDataRow119
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
