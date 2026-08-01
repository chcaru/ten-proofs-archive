
import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_353 :
    factorRowEncodingIsValid 353 = true ∧
      fullGramRowEncodingIsValid 353 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk014
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk011
  unfold coefficientFullGramDataRow coefficientFullGramDataRow353
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
