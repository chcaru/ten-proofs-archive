


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_166 :
    factorRowEncodingIsValid 166 = true ∧
      fullGramRowEncodingIsValid 166 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk006
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk005
  unfold coefficientFullGramDataRow coefficientFullGramDataRow166
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
