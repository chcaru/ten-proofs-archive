


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_315 :
    factorRowEncodingIsValid 315 = true ∧
      fullGramRowEncodingIsValid 315 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk012
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk009
  unfold coefficientFullGramDataRow coefficientFullGramDataRow315
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
