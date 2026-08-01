


import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseSoundness



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option linter.style.maxHeartbeats false

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_012 :
    orbitRadixNormalizedGramRowCheck 12 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_013 :
    orbitRadixNormalizedGramRowCheck 13 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_014 :
    orbitRadixNormalizedGramRowCheck 14 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_015 :
    orbitRadixNormalizedGramRowCheck 15 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
