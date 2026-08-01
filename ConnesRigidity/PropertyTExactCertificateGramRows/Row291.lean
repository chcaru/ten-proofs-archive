
import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_291 :
    factorRowEncodingIsValid 291 = true ∧
      fullGramRowEncodingIsValid 291 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk011
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk009
  unfold coefficientFullGramDataRow coefficientFullGramDataRow291
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
