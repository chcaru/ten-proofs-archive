


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_00 :
    blockFactorIdentityBlockCheck 0 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_00 :
    blockResidualSymmetryBlockCheck 0 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_00 :
    blockResidualDominanceBlockCheck 0 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
