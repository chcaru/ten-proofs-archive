


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_17 :
    blockFactorIdentityBlockCheck 17 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_17 :
    blockResidualSymmetryBlockCheck 17 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_17 :
    blockResidualDominanceBlockCheck 17 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
