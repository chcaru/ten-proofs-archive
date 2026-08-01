


import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseSoundness



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option linter.style.maxHeartbeats false

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_016 :
    orbitRadixNormalizedGramRowCheck 16 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_017 :
    orbitRadixNormalizedGramRowCheck 17 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_018 :
    orbitRadixNormalizedGramRowCheck 18 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_019 :
    orbitRadixNormalizedGramRowCheck 19 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
