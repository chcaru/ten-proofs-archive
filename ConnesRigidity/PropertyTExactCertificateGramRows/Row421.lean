


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_421 :
    factorRowEncodingIsValid 421 = true ∧
      fullGramRowEncodingIsValid 421 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk016
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk013
  unfold coefficientFullGramDataRow coefficientFullGramDataRow421
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
