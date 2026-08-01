


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_20 :
    blockFactorIdentityBlockCheck 20 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_20 :
    blockResidualSymmetryBlockCheck 20 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_20 :
    blockResidualDominanceBlockCheck 20 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
