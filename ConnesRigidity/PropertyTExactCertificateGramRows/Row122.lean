


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_122 :
    factorRowEncodingIsValid 122 = true ∧
      fullGramRowEncodingIsValid 122 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk004
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk003
  unfold coefficientFullGramDataRow coefficientFullGramDataRow122
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
