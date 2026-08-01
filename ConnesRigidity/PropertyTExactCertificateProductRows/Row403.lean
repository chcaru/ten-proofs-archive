
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_403 :
    productIndexRowIsValid 403 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange212_425
      productIndexDataRowRange318_425
      productIndexDataRowRange371_425
      productIndexDataRowRange398_425
      productIndexDataRowRange398_411
      productIndexDataRowRange398_404
      productIndexDataRowRange401_404
      productIndexDataRowRange402_404
      productIndexDataRow403
  | unfold productIndexDataRows productIndexDataRow403
  | unfold productIndexDataRow403
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
