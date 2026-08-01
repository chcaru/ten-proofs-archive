


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_246 :
    productIndexRowIsValid 246 = true := by
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
      productIndexDataRowRange244_247
      productIndexDataRowRange245_247
      productIndexDataRow246
  | unfold productIndexDataRows productIndexDataRow246
  | unfold productIndexDataRow246
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
