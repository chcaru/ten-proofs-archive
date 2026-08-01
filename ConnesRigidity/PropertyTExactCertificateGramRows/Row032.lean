
import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_032 :
    factorRowEncodingIsValid 32 = true ∧
      fullGramRowEncodingIsValid 32 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk001
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk001
  unfold coefficientFullGramDataRow coefficientFullGramDataRow032
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
