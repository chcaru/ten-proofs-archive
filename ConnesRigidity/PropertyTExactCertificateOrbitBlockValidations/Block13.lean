
import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_13 :
    blockFactorIdentityBlockCheck 13 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_13 :
    blockResidualSymmetryBlockCheck 13 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_13 :
    blockResidualDominanceBlockCheck 13 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
