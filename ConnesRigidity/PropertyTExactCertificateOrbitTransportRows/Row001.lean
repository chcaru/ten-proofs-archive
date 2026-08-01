


import ConnesRigidity.PropertyTExactCertificateOrbitCheckers

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem orbitSymmetryInverseRowCheck_001_valid :
    orbitSymmetryInverseRowCheck 1 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
