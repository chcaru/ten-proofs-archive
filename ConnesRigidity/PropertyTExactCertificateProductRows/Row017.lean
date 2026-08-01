
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_017 :
    productIndexRowIsValid 17 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange000_106
      productIndexDataRowRange000_053
      productIndexDataRowRange000_026
      productIndexDataRowRange013_026
      productIndexDataRowRange013_019
      productIndexDataRowRange016_019
      productIndexDataRowRange017_019
      productIndexDataRow017
  | unfold productIndexDataRows productIndexDataRow017
  | unfold productIndexDataRow017
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
