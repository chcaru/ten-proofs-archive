
import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_25 :
    blockFactorIdentityBlockCheck 25 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_25 :
    blockResidualSymmetryBlockCheck 25 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_25 :
    blockResidualDominanceBlockCheck 25 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
