
import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_339 :
    factorRowEncodingIsValid 339 = true ∧
      fullGramRowEncodingIsValid 339 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk013
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk010
  unfold coefficientFullGramDataRow coefficientFullGramDataRow339
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
