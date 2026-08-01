


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_422 :
    factorRowEncodingIsValid 422 = true ∧
      fullGramRowEncodingIsValid 422 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk016
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk013
  unfold coefficientFullGramDataRow coefficientFullGramDataRow422
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
