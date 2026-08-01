


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_202 :
    factorRowEncodingIsValid 202 = true ∧
      fullGramRowEncodingIsValid 202 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk008
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk006
  unfold coefficientFullGramDataRow coefficientFullGramDataRow202
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
