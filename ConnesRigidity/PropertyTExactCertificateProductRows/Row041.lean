


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_041 :
    productIndexRowIsValid 41 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange000_106
      productIndexDataRowRange000_053
      productIndexDataRowRange026_053
      productIndexDataRowRange039_053
      productIndexDataRowRange039_046
      productIndexDataRowRange039_042
      productIndexDataRowRange040_042
      productIndexDataRow041
  | unfold productIndexDataRows productIndexDataRow041
  | unfold productIndexDataRow041
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
