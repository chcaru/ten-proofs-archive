


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_126 :
    factorRowEncodingIsValid 126 = true ∧
      fullGramRowEncodingIsValid 126 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk005
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk003
  unfold coefficientFullGramDataRow coefficientFullGramDataRow126
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
