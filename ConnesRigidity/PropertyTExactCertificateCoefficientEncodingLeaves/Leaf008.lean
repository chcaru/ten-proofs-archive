


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf008.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_008 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf008.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_008 :
    coefficientCheckData (coefficientFactorTermChunk008) =
      (coefficientSourceEncoding_008,
        1042265902037344) := by
  unfold coefficientCheckData coefficientSourceEncoding_008
  unfold coefficientFactorTermChunk008
    coefficientFactorTermRowData
    coefficientFullGramDataRow080
    coefficientFullGramDataRow081
    coefficientFullGramDataRow082
    coefficientFullGramDataRow083
    coefficientFullGramDataRow084
    coefficientFullGramDataRow085
    coefficientFullGramDataRow086
    coefficientFullGramDataRow087
    coefficientFullGramDataRow088
    coefficientFullGramDataRow089
    productIndexDataRow080
    productIndexDataRow081
    productIndexDataRow082
    productIndexDataRow083
    productIndexDataRow084
    productIndexDataRow085
    productIndexDataRow086
    productIndexDataRow087
    productIndexDataRow088
    productIndexDataRow089
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
