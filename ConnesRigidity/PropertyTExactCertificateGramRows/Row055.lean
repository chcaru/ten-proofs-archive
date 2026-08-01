


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_055 :
    factorRowEncodingIsValid 55 = true ∧
      fullGramRowEncodingIsValid 55 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk002
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk001
  unfold coefficientFullGramDataRow coefficientFullGramDataRow055
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
