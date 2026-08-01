


import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseSoundness



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option linter.style.maxHeartbeats false

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_020 :
    orbitRadixNormalizedGramRowCheck 20 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_021 :
    orbitRadixNormalizedGramRowCheck 21 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_022 :
    orbitRadixNormalizedGramRowCheck 22 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_023 :
    orbitRadixNormalizedGramRowCheck 23 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
