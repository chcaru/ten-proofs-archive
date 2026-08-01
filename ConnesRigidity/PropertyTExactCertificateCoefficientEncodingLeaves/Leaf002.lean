
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf002.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_002 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf002.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_002 :
    coefficientCheckData (coefficientFactorTermChunk002) =
      (coefficientSourceEncoding_002,
        3563823739177936) := by
  unfold coefficientCheckData coefficientSourceEncoding_002
  unfold coefficientFactorTermChunk002
    coefficientFactorTermRowData
    coefficientFullGramDataRow020
    coefficientFullGramDataRow021
    coefficientFullGramDataRow022
    coefficientFullGramDataRow023
    coefficientFullGramDataRow024
    coefficientFullGramDataRow025
    coefficientFullGramDataRow026
    coefficientFullGramDataRow027
    coefficientFullGramDataRow028
    coefficientFullGramDataRow029
    productIndexDataRow020
    productIndexDataRow021
    productIndexDataRow022
    productIndexDataRow023
    productIndexDataRow024
    productIndexDataRow025
    productIndexDataRow026
    productIndexDataRow027
    productIndexDataRow028
    productIndexDataRow029
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
