


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_24 :
    blockFactorIdentityBlockCheck 24 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_24 :
    blockResidualSymmetryBlockCheck 24 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_24 :
    blockResidualDominanceBlockCheck 24 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
