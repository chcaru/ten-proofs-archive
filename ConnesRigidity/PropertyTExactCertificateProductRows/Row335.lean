
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_335 :
    productIndexRowIsValid 335 = true := by
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
      productIndexDataRowRange334_337
      productIndexDataRowRange335_337
      productIndexDataRow335
  | unfold productIndexDataRows productIndexDataRow335
  | unfold productIndexDataRow335
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
