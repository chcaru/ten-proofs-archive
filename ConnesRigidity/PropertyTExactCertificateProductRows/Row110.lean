
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_110 :
    productIndexRowIsValid 110 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange106_212
      productIndexDataRowRange106_159
      productIndexDataRowRange106_132
      productIndexDataRowRange106_119
      productIndexDataRowRange106_112
      productIndexDataRowRange109_112
      productIndexDataRowRange110_112
      productIndexDataRow110
  | unfold productIndexDataRows productIndexDataRow110
  | unfold productIndexDataRow110
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
