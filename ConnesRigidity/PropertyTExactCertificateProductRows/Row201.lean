


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_201 :
    productIndexRowIsValid 201 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange106_212
      productIndexDataRowRange159_212
      productIndexDataRowRange185_212
      productIndexDataRowRange198_212
      productIndexDataRowRange198_205
      productIndexDataRowRange201_205
      productIndexDataRowRange201_203
      productIndexDataRow201
  | unfold productIndexDataRows productIndexDataRow201
  | unfold productIndexDataRow201
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
