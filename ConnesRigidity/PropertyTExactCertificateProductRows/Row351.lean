


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_351 :
    productIndexRowIsValid 351 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange212_425
      productIndexDataRowRange318_425
      productIndexDataRowRange318_371
      productIndexDataRowRange344_371
      productIndexDataRowRange344_357
      productIndexDataRowRange350_357
      productIndexDataRowRange350_353
      productIndexDataRowRange351_353
      productIndexDataRow351
  | unfold productIndexDataRows productIndexDataRow351
  | unfold productIndexDataRow351
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
