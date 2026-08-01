


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_247 :
    factorRowEncodingIsValid 247 = true ∧
      fullGramRowEncodingIsValid 247 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk009
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk007
  unfold coefficientFullGramDataRow coefficientFullGramDataRow247
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
