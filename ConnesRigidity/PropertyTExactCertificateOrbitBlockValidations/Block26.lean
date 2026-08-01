


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_26 :
    blockFactorIdentityBlockCheck 26 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_26 :
    blockResidualSymmetryBlockCheck 26 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_26 :
    blockResidualDominanceBlockCheck 26 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
