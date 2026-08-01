


import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseSoundness



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option linter.style.maxHeartbeats false

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_008 :
    orbitRadixNormalizedGramRowCheck 8 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_009 :
    orbitRadixNormalizedGramRowCheck 9 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_010 :
    orbitRadixNormalizedGramRowCheck 10 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_011 :
    orbitRadixNormalizedGramRowCheck 11 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
