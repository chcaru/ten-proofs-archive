


import ConnesRigidity.PropertyTExactCertificateOrbitBlockMatrices



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in
theorem orbitBlockFactorIdentityBlockCheck_27 :
    blockFactorIdentityBlockCheck 27 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualSymmetryBlockCheck_27 :
    blockResidualSymmetryBlockCheck 27 = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem orbitBlockResidualDominanceBlockCheck_27 :
    blockResidualDominanceBlockCheck 27 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
