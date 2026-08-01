


import ConnesRigidity.PropertyTExactCertificateOrbitCheckers

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem orbitSymmetryInverseRowCheck_042_valid :
    orbitSymmetryInverseRowCheck 42 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
