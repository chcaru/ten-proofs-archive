
import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_143 :
    factorRowEncodingIsValid 143 = true ∧
      fullGramRowEncodingIsValid 143 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk005
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk004
  unfold coefficientFullGramDataRow coefficientFullGramDataRow143
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
