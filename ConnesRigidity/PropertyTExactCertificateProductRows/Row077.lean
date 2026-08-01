


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_077 :
    productIndexRowIsValid 77 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange000_212
      productIndexDataRowRange000_106
      productIndexDataRowRange053_106
      productIndexDataRowRange053_079
      productIndexDataRowRange066_079
      productIndexDataRowRange072_079
      productIndexDataRowRange075_079
      productIndexDataRowRange077_079
      productIndexDataRow077
  | unfold productIndexDataRows productIndexDataRow077
  | unfold productIndexDataRow077
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
