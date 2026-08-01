


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_370 :
    factorRowEncodingIsValid 370 = true ∧
      fullGramRowEncodingIsValid 370 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk014
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk011
  unfold coefficientFullGramDataRow coefficientFullGramDataRow370
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
