


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_02 :
    blockFactorIdentityBlockCheck 2 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_02 :
    blockResidualSymmetryBlockCheck 2 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_02 :
    blockResidualDominanceBlockCheck 2 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
