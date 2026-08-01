


import ConnesRigidity.PropertyTExactCertificateOrbitCheckers



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in

theorem orbitRowSumRowCheck_11 : orbitRowSumRowCheck 11 = true := by
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
