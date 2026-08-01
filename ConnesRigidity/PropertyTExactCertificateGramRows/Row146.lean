
import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_146 :
    factorRowEncodingIsValid 146 = true ∧
      fullGramRowEncodingIsValid 146 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk005
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk004
  unfold coefficientFullGramDataRow coefficientFullGramDataRow146
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
