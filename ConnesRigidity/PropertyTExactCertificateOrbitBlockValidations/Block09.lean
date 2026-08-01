


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_09 :
    blockFactorIdentityBlockCheck 9 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_09 :
    blockResidualSymmetryBlockCheck 9 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_09 :
    blockResidualDominanceBlockCheck 9 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
