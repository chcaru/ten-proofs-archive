


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_300 :
    productIndexRowIsValid 300 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange212_425
      productIndexDataRowRange212_318
      productIndexDataRowRange265_318
      productIndexDataRowRange291_318
      productIndexDataRowRange291_304
      productIndexDataRowRange297_304
      productIndexDataRowRange300_304
      productIndexDataRowRange300_302
      productIndexDataRow300
  | unfold productIndexDataRows productIndexDataRow300
  | unfold productIndexDataRow300
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
