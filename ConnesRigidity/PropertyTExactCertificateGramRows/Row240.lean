


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_240 :
    factorRowEncodingIsValid 240 = true ∧
      fullGramRowEncodingIsValid 240 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk009
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk007
  unfold coefficientFullGramDataRow coefficientFullGramDataRow240
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
