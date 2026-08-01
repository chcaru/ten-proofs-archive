
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf003.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_003 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf003.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_003 :
    coefficientCheckData (coefficientFactorTermChunk003) =
      (coefficientSourceEncoding_003,
        660667429655904) := by
  unfold coefficientCheckData coefficientSourceEncoding_003
  unfold coefficientFactorTermChunk003
    coefficientFactorTermRowData
    coefficientFullGramDataRow030
    coefficientFullGramDataRow031
    coefficientFullGramDataRow032
    coefficientFullGramDataRow033
    coefficientFullGramDataRow034
    coefficientFullGramDataRow035
    coefficientFullGramDataRow036
    coefficientFullGramDataRow037
    coefficientFullGramDataRow038
    coefficientFullGramDataRow039
    productIndexDataRow030
    productIndexDataRow031
    productIndexDataRow032
    productIndexDataRow033
    productIndexDataRow034
    productIndexDataRow035
    productIndexDataRow036
    productIndexDataRow037
    productIndexDataRow038
    productIndexDataRow039
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
