


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative030
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_030 :
    coefficientNegativePacketTerms030 =
      (negativeEdgeTerms.drop 15360).take 512 := by
  unfold coefficientNegativePacketTerms030 coefficientNegativePacketRows030
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
