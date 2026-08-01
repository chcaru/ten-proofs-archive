
import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_288 :
    productIndexRowIsValid 288 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange212_425
      productIndexDataRowRange212_318
      productIndexDataRowRange265_318
      productIndexDataRowRange265_291
      productIndexDataRowRange278_291
      productIndexDataRowRange284_291
      productIndexDataRowRange287_291
      productIndexDataRowRange287_289
      productIndexDataRow288
  | unfold productIndexDataRows productIndexDataRow288
  | unfold productIndexDataRow288
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
