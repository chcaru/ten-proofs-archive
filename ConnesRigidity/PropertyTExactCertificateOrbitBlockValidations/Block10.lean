


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_10 :
    blockFactorIdentityBlockCheck 10 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_10 :
    blockResidualSymmetryBlockCheck 10 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_10 :
    blockResidualDominanceBlockCheck 10 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
