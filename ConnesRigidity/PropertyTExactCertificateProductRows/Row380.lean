


import ConnesRigidity.PropertyTExactCertificateProductBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem productRowCheck_380 :
    productIndexRowIsValid 380 = true := by
  unfold productIndexRowIsValid
  unfold productIndexDataRow
  first
  | unfold productIndexDataRowRange000_425
      productIndexDataRowRange212_425
      productIndexDataRowRange318_425
      productIndexDataRowRange371_425
      productIndexDataRowRange371_398
      productIndexDataRowRange371_384
      productIndexDataRowRange377_384
      productIndexDataRowRange380_384
      productIndexDataRowRange380_382
      productIndexDataRow380
  | unfold productIndexDataRows productIndexDataRow380
  | unfold productIndexDataRow380
  unfold basisDataArray
  unfold productIndexEntriesAreValid productIndexEntryIsValid
    rawAffineProductMatchesArray
  unfold allElementDataRow allElementDataGroups
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
