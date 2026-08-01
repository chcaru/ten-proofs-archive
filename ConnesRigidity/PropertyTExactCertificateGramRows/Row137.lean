
import ConnesRigidity.PropertyTExactCertificateGramBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem gramRowCheck_137 :
    factorRowEncodingIsValid 137 = true ∧
      fullGramRowEncodingIsValid 137 = true := by
  unfold factorRowEncodingIsValid fullGramRowEncodingIsValid
  unfold factorCoefficientRow factorCoefficientRowOf factorRow
    factorRowChunk factorRowChunk005
  unfold encodedFullGramColumnCombination
  unfold factorColumn factorColumnChunk factorColumnChunk004
  unfold coefficientFullGramDataRow coefficientFullGramDataRow137
  unfold encodedFactorRows encodedFactorRowData
  unfold encodeGramRow gramEncodingBase
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
