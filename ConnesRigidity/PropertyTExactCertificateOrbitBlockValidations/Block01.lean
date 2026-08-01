
import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_01 :
    blockFactorIdentityBlockCheck 1 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_01 :
    blockResidualSymmetryBlockCheck 1 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_01 :
    blockResidualDominanceBlockCheck 1 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
