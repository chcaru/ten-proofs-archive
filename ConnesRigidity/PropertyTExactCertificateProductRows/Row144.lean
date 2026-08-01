


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_144 :
    productIndexRowIsValid 144 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange106_212
      productIndexDataRowRange106_159
      productIndexDataRowRange132_159
      productIndexDataRowRange132_145
      productIndexDataRowRange138_145
      productIndexDataRowRange141_145
      productIndexDataRowRange143_145
      productIndexDataRow144
  | unfold productIndexDataRows productIndexDataRow144
  | unfold productIndexDataRow144
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
