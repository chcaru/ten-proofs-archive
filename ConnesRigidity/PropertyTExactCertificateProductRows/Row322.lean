
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_322 :
    productIndexRowIsValid 322 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange212_425
      productIndexDataRowRange318_425
      productIndexDataRowRange318_371
      productIndexDataRowRange318_344
      productIndexDataRowRange318_331
      productIndexDataRowRange318_324
      productIndexDataRowRange321_324
      productIndexDataRowRange322_324
      productIndexDataRow322
  | unfold productIndexDataRows productIndexDataRow322
  | unfold productIndexDataRow322
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
