
import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_03 :
    blockFactorIdentityBlockCheck 3 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_03 :
    blockResidualSymmetryBlockCheck 3 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_03 :
    blockResidualDominanceBlockCheck 3 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
