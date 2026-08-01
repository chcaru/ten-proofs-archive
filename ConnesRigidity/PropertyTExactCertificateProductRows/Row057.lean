
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_057 :
    productIndexRowIsValid 57 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange000_106
      productIndexDataRowRange053_106
      productIndexDataRowRange053_079
      productIndexDataRowRange053_066
      productIndexDataRowRange053_059
      productIndexDataRowRange056_059
      productIndexDataRowRange057_059
      productIndexDataRow057
  | unfold productIndexDataRows productIndexDataRow057
  | unfold productIndexDataRow057
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
