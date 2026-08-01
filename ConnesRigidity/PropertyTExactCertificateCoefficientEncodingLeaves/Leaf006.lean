


import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf006.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_006 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf006.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_006 :
    coefficientCheckData (coefficientFactorTermChunk006) =
      (coefficientSourceEncoding_006,
        777962017215696) := by
  unfold coefficientCheckData coefficientSourceEncoding_006
  unfold coefficientFactorTermChunk006
    coefficientFactorTermRowData
    coefficientFullGramDataRow060
    coefficientFullGramDataRow061
    coefficientFullGramDataRow062
    coefficientFullGramDataRow063
    coefficientFullGramDataRow064
    coefficientFullGramDataRow065
    coefficientFullGramDataRow066
    coefficientFullGramDataRow067
    coefficientFullGramDataRow068
    coefficientFullGramDataRow069
    productIndexDataRow060
    productIndexDataRow061
    productIndexDataRow062
    productIndexDataRow063
    productIndexDataRow064
    productIndexDataRow065
    productIndexDataRow066
    productIndexDataRow067
    productIndexDataRow068
    productIndexDataRow069
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
