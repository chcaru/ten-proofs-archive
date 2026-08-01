


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_039 :
    factorRowEncodingIsValid 39 = true ∧
      fullGramRowEncodingIsValid 39 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk001
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk001
  unfold coefficientFullGramDataRow coefficientFullGramDataRow039
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
