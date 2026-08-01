import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientTransportValidation

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option linter.style.setOption false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem orbitCoefficientTransportPacketsBatch10_valid :
    orbitCoefficientTransportPacketsCheck 1880
      ((gramOrbitData.toList.drop 1880).take 188)
      ((orbitCoefficientTransportPacketData.drop 1880).take 188) = true := by
  decide +kernel

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
