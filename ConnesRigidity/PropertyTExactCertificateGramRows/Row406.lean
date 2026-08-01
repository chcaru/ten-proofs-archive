


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_406 :
    factorRowEncodingIsValid 406 = true ∧
      fullGramRowEncodingIsValid 406 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk016
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk012
  unfold coefficientFullGramDataRow coefficientFullGramDataRow406
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
