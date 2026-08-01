
import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseSoundness

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option linter.style.maxHeartbeats false

set_option maxHeartbeats 64000000 in
theorem orbitRadixDenseGramRowCheck_000 :
    orbitRadixDenseGramRowCheck 0 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixDenseGramRowCheck_001 :
    orbitRadixDenseGramRowCheck 1 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixDenseGramRowCheck_002 :
    orbitRadixDenseGramRowCheck 2 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixDenseGramRowCheck_003 :
    orbitRadixDenseGramRowCheck 3 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixDenseGramRowCheck_004 :
    orbitRadixDenseGramRowCheck 4 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixDenseGramRowCheck_005 :
    orbitRadixDenseGramRowCheck 5 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixDenseGramRowCheck_006 :
    orbitRadixDenseGramRowCheck 6 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixDenseGramRowCheck_007 :
    orbitRadixDenseGramRowCheck 7 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
