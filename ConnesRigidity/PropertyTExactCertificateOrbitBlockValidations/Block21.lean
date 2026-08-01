
import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_21 :
    blockFactorIdentityBlockCheck 21 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_21 :
    blockResidualSymmetryBlockCheck 21 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_21 :
    blockResidualDominanceBlockCheck 21 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
