


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_151 :
    factorRowEncodingIsValid 151 = true ∧
      fullGramRowEncodingIsValid 151 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk006
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk004
  unfold coefficientFullGramDataRow coefficientFullGramDataRow151
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
