


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_12 :
    blockFactorIdentityBlockCheck 12 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_12 :
    blockResidualSymmetryBlockCheck 12 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_12 :
    blockResidualDominanceBlockCheck 12 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
