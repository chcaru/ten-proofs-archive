


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_14 :
    blockFactorIdentityBlockCheck 14 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_14 :
    blockResidualSymmetryBlockCheck 14 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_14 :
    blockResidualDominanceBlockCheck 14 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
