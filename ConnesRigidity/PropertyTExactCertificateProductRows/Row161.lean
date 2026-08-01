
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_161 :
    productIndexRowIsValid 161 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange106_212
      productIndexDataRowRange159_212
      productIndexDataRowRange159_185
      productIndexDataRowRange159_172
      productIndexDataRowRange159_165
      productIndexDataRowRange159_162
      productIndexDataRowRange160_162
      productIndexDataRow161
  | unfold productIndexDataRows productIndexDataRow161
  | unfold productIndexDataRow161
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
