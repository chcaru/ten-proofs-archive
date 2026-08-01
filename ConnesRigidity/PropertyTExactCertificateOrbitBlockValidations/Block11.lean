


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_11 :
    blockFactorIdentityBlockCheck 11 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_11 :
    blockResidualSymmetryBlockCheck 11 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_11 :
    blockResidualDominanceBlockCheck 11 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
