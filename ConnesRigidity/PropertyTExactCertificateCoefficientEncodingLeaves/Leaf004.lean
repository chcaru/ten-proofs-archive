
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf004.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_004 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf004.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_004 :
    coefficientCheckData (coefficientFactorTermChunk004) =
      (coefficientSourceEncoding_004,
        718821124247536) := by
  unfold coefficientCheckData coefficientSourceEncoding_004
  unfold coefficientFactorTermChunk004
    coefficientFactorTermRowData
    coefficientFullGramDataRow040
    coefficientFullGramDataRow041
    coefficientFullGramDataRow042
    coefficientFullGramDataRow043
    coefficientFullGramDataRow044
    coefficientFullGramDataRow045
    coefficientFullGramDataRow046
    coefficientFullGramDataRow047
    coefficientFullGramDataRow048
    coefficientFullGramDataRow049
    productIndexDataRow040
    productIndexDataRow041
    productIndexDataRow042
    productIndexDataRow043
    productIndexDataRow044
    productIndexDataRow045
    productIndexDataRow046
    productIndexDataRow047
    productIndexDataRow048
    productIndexDataRow049
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
