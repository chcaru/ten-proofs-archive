


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_031 :
    productIndexRowIsValid 31 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange000_106
      productIndexDataRowRange000_053
      productIndexDataRowRange026_053
      productIndexDataRowRange026_039
      productIndexDataRowRange026_032
      productIndexDataRowRange029_032
      productIndexDataRowRange030_032
      productIndexDataRow031
  | unfold productIndexDataRows productIndexDataRow031
  | unfold productIndexDataRow031
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
