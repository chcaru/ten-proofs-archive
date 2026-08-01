


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_325 :
    productIndexRowIsValid 325 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange212_425
      productIndexDataRowRange318_425
      productIndexDataRowRange318_371
      productIndexDataRowRange318_344
      productIndexDataRowRange318_331
      productIndexDataRowRange324_331
      productIndexDataRowRange324_327
      productIndexDataRowRange325_327
      productIndexDataRow325
  | unfold productIndexDataRows productIndexDataRow325
  | unfold productIndexDataRow325
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
