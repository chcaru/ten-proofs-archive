
import ConnesRigidity.PropertyTExactCertificateOrbitCheckers

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem orbitSymmetryInverseRowCheck_026_valid :
    orbitSymmetryInverseRowCheck 26 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
