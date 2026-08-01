
import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_16 :
    blockFactorIdentityBlockCheck 16 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_16 :
    blockResidualSymmetryBlockCheck 16 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_16 :
    blockResidualDominanceBlockCheck 16 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
