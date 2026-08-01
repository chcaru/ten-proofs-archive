
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_253 :
    productIndexRowIsValid 253 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange212_425
      productIndexDataRowRange212_318
      productIndexDataRowRange212_265
      productIndexDataRowRange238_265
      productIndexDataRowRange251_265
      productIndexDataRowRange251_258
      productIndexDataRowRange251_254
      productIndexDataRowRange252_254
      productIndexDataRow253
  | unfold productIndexDataRows productIndexDataRow253
  | unfold productIndexDataRow253
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
