


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_033 :
    productIndexRowIsValid 33 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange000_106
      productIndexDataRowRange000_053
      productIndexDataRowRange026_053
      productIndexDataRowRange026_039
      productIndexDataRowRange032_039
      productIndexDataRowRange032_035
      productIndexDataRowRange033_035
      productIndexDataRow033
  | unfold productIndexDataRows productIndexDataRow033
  | unfold productIndexDataRow033
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
