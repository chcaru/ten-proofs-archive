


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_15 :
    blockFactorIdentityBlockCheck 15 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_15 :
    blockResidualSymmetryBlockCheck 15 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_15 :
    blockResidualDominanceBlockCheck 15 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
