


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_07 :
    blockFactorIdentityBlockCheck 7 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_07 :
    blockResidualSymmetryBlockCheck 7 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_07 :
    blockResidualDominanceBlockCheck 7 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
