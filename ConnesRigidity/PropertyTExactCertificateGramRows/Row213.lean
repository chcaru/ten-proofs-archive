
import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_213 :
    factorRowEncodingIsValid 213 = true ∧
      fullGramRowEncodingIsValid 213 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk008
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk006
  unfold coefficientFullGramDataRow coefficientFullGramDataRow213
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
