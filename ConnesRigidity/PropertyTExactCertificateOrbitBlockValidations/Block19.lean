
import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_19 :
    blockFactorIdentityBlockCheck 19 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_19 :
    blockResidualSymmetryBlockCheck 19 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_19 :
    blockResidualDominanceBlockCheck 19 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
