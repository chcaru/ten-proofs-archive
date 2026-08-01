


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_18 :
    blockFactorIdentityBlockCheck 18 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_18 :
    blockResidualSymmetryBlockCheck 18 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_18 :
    blockResidualDominanceBlockCheck 18 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
