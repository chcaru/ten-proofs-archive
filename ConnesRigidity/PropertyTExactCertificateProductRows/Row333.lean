


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_333 :
    productIndexRowIsValid 333 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange212_425
      productIndexDataRowRange318_425
      productIndexDataRowRange318_371
      productIndexDataRowRange318_344
      productIndexDataRowRange331_344
      productIndexDataRowRange331_337
      productIndexDataRowRange331_334
      productIndexDataRowRange332_334
      productIndexDataRow333
  | unfold productIndexDataRows productIndexDataRow333
  | unfold productIndexDataRow333
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
