


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative010
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_010 :
    coefficientNegativePacketTerms010 =
      (negativeEdgeTerms.drop 5120).take 512 := by
  unfold coefficientNegativePacketTerms010 coefficientNegativePacketRows010
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
