


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_197 :
    productIndexRowIsValid 197 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange106_212
      productIndexDataRowRange159_212
      productIndexDataRowRange185_212
      productIndexDataRowRange185_198
      productIndexDataRowRange191_198
      productIndexDataRowRange194_198
      productIndexDataRowRange196_198
      productIndexDataRow197
  | unfold productIndexDataRows productIndexDataRow197
  | unfold productIndexDataRow197
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
