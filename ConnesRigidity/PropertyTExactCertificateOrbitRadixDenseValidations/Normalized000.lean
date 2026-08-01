


import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseSoundness



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option linter.style.maxHeartbeats false

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_000 :
    orbitRadixNormalizedGramRowCheck 0 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_001 :
    orbitRadixNormalizedGramRowCheck 1 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_002 :
    orbitRadixNormalizedGramRowCheck 2 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_003 :
    orbitRadixNormalizedGramRowCheck 3 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
