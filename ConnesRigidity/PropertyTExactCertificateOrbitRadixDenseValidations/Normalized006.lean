
import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseSoundness

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option linter.style.maxHeartbeats false

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_024 :
    orbitRadixNormalizedGramRowCheck 24 = true := by
  decide +kernel

set_option maxHeartbeats 64000000 in
theorem orbitRadixNormalizedGramRowCheck_025 :
    orbitRadixNormalizedGramRowCheck 25 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
