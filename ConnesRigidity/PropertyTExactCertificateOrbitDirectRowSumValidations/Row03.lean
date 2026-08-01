


import ConnesRigidity.PropertyTExactCertificateOrbitCheckers



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000

set_option maxHeartbeats 16000000 in

theorem orbitNormalizedRowGramSum_03 :
    (pairOrbitIndexData.getD 3 #[]).toList.foldl
      (fun total orbit => total + gramOrbitCoefficient orbit.toNat) 0 = 0 := by
  decide +kernel

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
