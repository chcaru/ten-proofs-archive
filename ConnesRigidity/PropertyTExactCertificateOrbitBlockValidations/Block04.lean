
import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_04 :
    blockFactorIdentityBlockCheck 4 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_04 :
    blockResidualSymmetryBlockCheck 4 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_04 :
    blockResidualDominanceBlockCheck 4 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
