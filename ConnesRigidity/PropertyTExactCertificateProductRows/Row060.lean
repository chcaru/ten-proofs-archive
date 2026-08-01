
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_060 :
    productIndexRowIsValid 60 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange000_106
      productIndexDataRowRange053_106
      productIndexDataRowRange053_079
      productIndexDataRowRange053_066
      productIndexDataRowRange059_066
      productIndexDataRowRange059_062
      productIndexDataRowRange060_062
      productIndexDataRow060
  | unfold productIndexDataRows productIndexDataRow060
  | unfold productIndexDataRow060
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
