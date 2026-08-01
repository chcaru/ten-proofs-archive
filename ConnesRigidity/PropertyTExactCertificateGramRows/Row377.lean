


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_377 :
    factorRowEncodingIsValid 377 = true ∧
      fullGramRowEncodingIsValid 377 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk015
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk011
  unfold coefficientFullGramDataRow coefficientFullGramDataRow377
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
