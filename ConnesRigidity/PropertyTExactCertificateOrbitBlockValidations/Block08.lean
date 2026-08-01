


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_08 :
    blockFactorIdentityBlockCheck 8 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_08 :
    blockResidualSymmetryBlockCheck 8 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_08 :
    blockResidualDominanceBlockCheck 8 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
