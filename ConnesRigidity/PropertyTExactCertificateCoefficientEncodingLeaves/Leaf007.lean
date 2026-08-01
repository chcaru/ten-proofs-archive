


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf007.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_007 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf007.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_007 :
    coefficientCheckData (coefficientFactorTermChunk007) =
      (coefficientSourceEncoding_007,
        880173099543952) := by
  unfold coefficientCheckData coefficientSourceEncoding_007
  unfold coefficientFactorTermChunk007
    coefficientFactorTermRowData
    coefficientFullGramDataRow070
    coefficientFullGramDataRow071
    coefficientFullGramDataRow072
    coefficientFullGramDataRow073
    coefficientFullGramDataRow074
    coefficientFullGramDataRow075
    coefficientFullGramDataRow076
    coefficientFullGramDataRow077
    coefficientFullGramDataRow078
    coefficientFullGramDataRow079
    productIndexDataRow070
    productIndexDataRow071
    productIndexDataRow072
    productIndexDataRow073
    productIndexDataRow074
    productIndexDataRow075
    productIndexDataRow076
    productIndexDataRow077
    productIndexDataRow078
    productIndexDataRow079
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
