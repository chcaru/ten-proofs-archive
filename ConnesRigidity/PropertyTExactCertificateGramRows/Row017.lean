
import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_017 :
    factorRowEncodingIsValid 17 = true ∧
      fullGramRowEncodingIsValid 17 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk000
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk000
  unfold coefficientFullGramDataRow coefficientFullGramDataRow017
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
