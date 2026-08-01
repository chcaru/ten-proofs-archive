


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_248 :
    productIndexRowIsValid 248 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange212_425
      productIndexDataRowRange212_318
      productIndexDataRowRange212_265
      productIndexDataRowRange238_265
      productIndexDataRowRange238_251
      productIndexDataRowRange244_251
      productIndexDataRowRange247_251
      productIndexDataRowRange247_249
      productIndexDataRow248
  | unfold productIndexDataRows productIndexDataRow248
  | unfold productIndexDataRow248
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
