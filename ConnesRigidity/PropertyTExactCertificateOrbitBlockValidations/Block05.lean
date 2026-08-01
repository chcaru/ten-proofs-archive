
import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_05 :
    blockFactorIdentityBlockCheck 5 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_05 :
    blockResidualSymmetryBlockCheck 5 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_05 :
    blockResidualDominanceBlockCheck 5 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
