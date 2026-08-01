


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_167 :
    productIndexRowIsValid 167 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange106_212
      productIndexDataRowRange159_212
      productIndexDataRowRange159_185
      productIndexDataRowRange159_172
      productIndexDataRowRange165_172
      productIndexDataRowRange165_168
      productIndexDataRowRange166_168
      productIndexDataRow167
  | unfold productIndexDataRows productIndexDataRow167
  | unfold productIndexDataRow167
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
