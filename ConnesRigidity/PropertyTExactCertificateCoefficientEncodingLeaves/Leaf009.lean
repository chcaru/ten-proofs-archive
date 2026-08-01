


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf009.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_009 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf009.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_009 :
    coefficientCheckData (coefficientFactorTermChunk009) =
      (coefficientSourceEncoding_009,
        873939545263856) := by
  unfold coefficientCheckData coefficientSourceEncoding_009
  unfold coefficientFactorTermChunk009
    coefficientFactorTermRowData
    coefficientFullGramDataRow090
    coefficientFullGramDataRow091
    coefficientFullGramDataRow092
    coefficientFullGramDataRow093
    coefficientFullGramDataRow094
    coefficientFullGramDataRow095
    coefficientFullGramDataRow096
    coefficientFullGramDataRow097
    coefficientFullGramDataRow098
    coefficientFullGramDataRow099
    productIndexDataRow090
    productIndexDataRow091
    productIndexDataRow092
    productIndexDataRow093
    productIndexDataRow094
    productIndexDataRow095
    productIndexDataRow096
    productIndexDataRow097
    productIndexDataRow098
    productIndexDataRow099
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
