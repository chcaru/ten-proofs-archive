


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative088
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_088 :
    coefficientNegativePacketTerms088 =
      (negativeEdgeTerms.drop 45056).take 512 := by
  unfold coefficientNegativePacketTerms088 coefficientNegativePacketRows088
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
