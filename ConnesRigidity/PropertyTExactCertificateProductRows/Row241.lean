
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_241 :
    productIndexRowIsValid 241 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange212_425
      productIndexDataRowRange212_318
      productIndexDataRowRange212_265
      productIndexDataRowRange238_265
      productIndexDataRowRange238_251
      productIndexDataRowRange238_244
      productIndexDataRowRange241_244
      productIndexDataRow241
  | unfold productIndexDataRows productIndexDataRow241
  | unfold productIndexDataRow241
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
