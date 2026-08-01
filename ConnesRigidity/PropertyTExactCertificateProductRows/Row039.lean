


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_039 :
    productIndexRowIsValid 39 = true := by
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
      productIndexDataRow039
  | unfold productIndexDataRows productIndexDataRow039
  | unfold productIndexDataRow039
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
