


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_294 :
    productIndexRowIsValid 294 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange212_425
      productIndexDataRowRange212_318
      productIndexDataRowRange265_318
      productIndexDataRowRange291_318
      productIndexDataRowRange291_304
      productIndexDataRowRange291_297
      productIndexDataRowRange294_297
      productIndexDataRow294
  | unfold productIndexDataRows productIndexDataRow294
  | unfold productIndexDataRow294
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
