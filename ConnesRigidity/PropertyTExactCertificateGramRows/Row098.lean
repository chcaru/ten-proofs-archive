


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_098 :
    factorRowEncodingIsValid 98 = true ∧
      fullGramRowEncodingIsValid 98 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk003
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk003
  unfold coefficientFullGramDataRow coefficientFullGramDataRow098
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
