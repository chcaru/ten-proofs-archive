
import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_296 :
    factorRowEncodingIsValid 296 = true ∧
      fullGramRowEncodingIsValid 296 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk011
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk009
  unfold coefficientFullGramDataRow coefficientFullGramDataRow296
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
