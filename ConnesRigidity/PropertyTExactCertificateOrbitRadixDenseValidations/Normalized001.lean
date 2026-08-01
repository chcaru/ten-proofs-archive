


import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseSoundness



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option linter.style.maxHeartbeats false

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_004 :
    orbitRadixNormalizedGramRowCheck 4 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_005 :
    orbitRadixNormalizedGramRowCheck 5 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_006 :
    orbitRadixNormalizedGramRowCheck 6 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_007 :
    orbitRadixNormalizedGramRowCheck 7 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
