
import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_268 :
    factorRowEncodingIsValid 268 = true ∧
      fullGramRowEncodingIsValid 268 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk010
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk008
  unfold coefficientFullGramDataRow coefficientFullGramDataRow268
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
