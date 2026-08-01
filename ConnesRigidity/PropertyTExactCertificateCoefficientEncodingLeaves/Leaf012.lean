
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf012.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_012 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf012.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_012 :
    coefficientCheckData (coefficientFactorTermChunk012) =
      (coefficientSourceEncoding_012,
        675690320432048) := by
  unfold coefficientCheckData coefficientSourceEncoding_012
  unfold coefficientFactorTermChunk012
    coefficientFactorTermRowData
    coefficientFullGramDataRow120
    coefficientFullGramDataRow121
    coefficientFullGramDataRow122
    coefficientFullGramDataRow123
    coefficientFullGramDataRow124
    coefficientFullGramDataRow125
    coefficientFullGramDataRow126
    coefficientFullGramDataRow127
    coefficientFullGramDataRow128
    coefficientFullGramDataRow129
    productIndexDataRow120
    productIndexDataRow121
    productIndexDataRow122
    productIndexDataRow123
    productIndexDataRow124
    productIndexDataRow125
    productIndexDataRow126
    productIndexDataRow127
    productIndexDataRow128
    productIndexDataRow129
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
