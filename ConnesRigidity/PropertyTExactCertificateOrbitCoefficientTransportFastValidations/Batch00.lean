import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientTransportValidation

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option linter.style.setOption false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0


theorem orbitCoefficientTransportPacketsBatch00_valid :
    orbitCoefficientTransportPacketsCheck 0
      ((gramOrbitData.toList.drop 0).take 188)
      ((orbitCoefficientTransportPacketData.drop 0).take 188) = true := by
  decide +kernel

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
