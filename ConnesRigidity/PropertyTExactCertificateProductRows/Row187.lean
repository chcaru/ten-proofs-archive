
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_187 :
    productIndexRowIsValid 187 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange106_212
      productIndexDataRowRange159_212
      productIndexDataRowRange185_212
      productIndexDataRowRange185_198
      productIndexDataRowRange185_191
      productIndexDataRowRange185_188
      productIndexDataRowRange186_188
      productIndexDataRow187
  | unfold productIndexDataRows productIndexDataRow187
  | unfold productIndexDataRow187
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
