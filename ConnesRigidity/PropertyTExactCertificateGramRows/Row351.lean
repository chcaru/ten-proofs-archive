
import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_351 :
    factorRowEncodingIsValid 351 = true ∧
      fullGramRowEncodingIsValid 351 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk014
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk010
  unfold coefficientFullGramDataRow coefficientFullGramDataRow351
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
