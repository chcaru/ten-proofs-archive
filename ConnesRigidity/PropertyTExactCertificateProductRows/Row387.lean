
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_387 :
    productIndexRowIsValid 387 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange212_425
      productIndexDataRowRange318_425
      productIndexDataRowRange371_425
      productIndexDataRowRange371_398
      productIndexDataRowRange384_398
      productIndexDataRowRange384_391
      productIndexDataRowRange387_391
      productIndexDataRowRange387_389
      productIndexDataRow387
  | unfold productIndexDataRows productIndexDataRow387
  | unfold productIndexDataRow387
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
