
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_116 :
    productIndexRowIsValid 116 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange106_212
      productIndexDataRowRange106_159
      productIndexDataRowRange106_132
      productIndexDataRowRange106_119
      productIndexDataRowRange112_119
      productIndexDataRowRange115_119
      productIndexDataRowRange115_117
      productIndexDataRow116
  | unfold productIndexDataRows productIndexDataRow116
  | unfold productIndexDataRow116
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
