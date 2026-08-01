
import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_23 :
    blockFactorIdentityBlockCheck 23 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_23 :
    blockResidualSymmetryBlockCheck 23 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_23 :
    blockResidualDominanceBlockCheck 23 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
