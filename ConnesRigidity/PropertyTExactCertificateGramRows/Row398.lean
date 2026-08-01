


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_398 :
    factorRowEncodingIsValid 398 = true ∧
      fullGramRowEncodingIsValid 398 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk015
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk012
  unfold coefficientFullGramDataRow coefficientFullGramDataRow398
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
