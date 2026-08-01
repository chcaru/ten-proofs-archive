
import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_088 :
    factorRowEncodingIsValid 88 = true ∧
      fullGramRowEncodingIsValid 88 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk003
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk002
  unfold coefficientFullGramDataRow coefficientFullGramDataRow088
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
