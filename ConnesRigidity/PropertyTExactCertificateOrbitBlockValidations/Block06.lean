


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_06 :
    blockFactorIdentityBlockCheck 6 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_06 :
    blockResidualSymmetryBlockCheck 6 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_06 :
    blockResidualDominanceBlockCheck 6 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
