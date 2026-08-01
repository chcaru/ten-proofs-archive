


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_22 :
    blockFactorIdentityBlockCheck 22 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_22 :
    blockResidualSymmetryBlockCheck 22 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_22 :
    blockResidualDominanceBlockCheck 22 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
