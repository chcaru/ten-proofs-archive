


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_130 :
    productIndexRowIsValid 130 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange106_212
      productIndexDataRowRange106_159
      productIndexDataRowRange106_132
      productIndexDataRowRange119_132
      productIndexDataRowRange125_132
      productIndexDataRowRange128_132
      productIndexDataRowRange130_132
      productIndexDataRow130
  | unfold productIndexDataRows productIndexDataRow130
  | unfold productIndexDataRow130
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
