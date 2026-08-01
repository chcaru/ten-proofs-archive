
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf005.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_005 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf005.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_005 :
    coefficientCheckData (coefficientFactorTermChunk005) =
      (coefficientSourceEncoding_005,
        660667436683392) := by
  unfold coefficientCheckData coefficientSourceEncoding_005
  unfold coefficientFactorTermChunk005
    coefficientFactorTermRowData
    coefficientFullGramDataRow050
    coefficientFullGramDataRow051
    coefficientFullGramDataRow052
    coefficientFullGramDataRow053
    coefficientFullGramDataRow054
    coefficientFullGramDataRow055
    coefficientFullGramDataRow056
    coefficientFullGramDataRow057
    coefficientFullGramDataRow058
    coefficientFullGramDataRow059
    productIndexDataRow050
    productIndexDataRow051
    productIndexDataRow052
    productIndexDataRow053
    productIndexDataRow054
    productIndexDataRow055
    productIndexDataRow056
    productIndexDataRow057
    productIndexDataRow058
    productIndexDataRow059
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
