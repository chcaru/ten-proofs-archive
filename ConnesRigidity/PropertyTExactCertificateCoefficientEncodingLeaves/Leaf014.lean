
import ConnesRigidity.PropertyTExactCertificateCoefficientEncodingBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf014.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_014 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Leaf014.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingLeafCheck_014 :
    coefficientCheckData (coefficientFactorTermChunk014) =
      (coefficientSourceEncoding_014,
        1043003878148912) := by
  unfold coefficientCheckData coefficientSourceEncoding_014
  unfold coefficientFactorTermChunk014
    coefficientFactorTermRowData
    coefficientFullGramDataRow140
    coefficientFullGramDataRow141
    coefficientFullGramDataRow142
    coefficientFullGramDataRow143
    coefficientFullGramDataRow144
    coefficientFullGramDataRow145
    coefficientFullGramDataRow146
    coefficientFullGramDataRow147
    coefficientFullGramDataRow148
    coefficientFullGramDataRow149
    productIndexDataRow140
    productIndexDataRow141
    productIndexDataRow142
    productIndexDataRow143
    productIndexDataRow144
    productIndexDataRow145
    productIndexDataRow146
    productIndexDataRow147
    productIndexDataRow148
    productIndexDataRow149
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
