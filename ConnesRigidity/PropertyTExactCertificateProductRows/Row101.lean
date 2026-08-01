


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_101 :
    productIndexRowIsValid 101 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange000_106
      productIndexDataRowRange053_106
      productIndexDataRowRange079_106
      productIndexDataRowRange092_106
      productIndexDataRowRange099_106
      productIndexDataRowRange099_102
      productIndexDataRowRange100_102
      productIndexDataRow101
  | unfold productIndexDataRows productIndexDataRow101
  | unfold productIndexDataRow101
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
