


import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_424 :
    fullGramRowEncodingIsValid 424 = true := by
  unfold fullGramRowEncodingIsValid
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk013
  unfold coefficientFullGramDataRow coefficientFullGramDataRow424
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
