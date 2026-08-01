
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_422 :
    productIndexRowIsValid 422 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange212_425
      productIndexDataRowRange318_425
      productIndexDataRowRange371_425
      productIndexDataRowRange398_425
      productIndexDataRowRange411_425
      productIndexDataRowRange418_425
      productIndexDataRowRange421_425
      productIndexDataRowRange421_423
      productIndexDataRow422
  | unfold productIndexDataRows productIndexDataRow422
  | unfold productIndexDataRow422
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
