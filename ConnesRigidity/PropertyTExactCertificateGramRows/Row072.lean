
import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_072 :
    factorRowEncodingIsValid 72 = true ∧
      fullGramRowEncodingIsValid 72 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk002
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk002
  unfold coefficientFullGramDataRow coefficientFullGramDataRow072
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
