


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_273 :
    factorRowEncodingIsValid 273 = true ∧
      fullGramRowEncodingIsValid 273 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk010
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk008
  unfold coefficientFullGramDataRow coefficientFullGramDataRow273
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
