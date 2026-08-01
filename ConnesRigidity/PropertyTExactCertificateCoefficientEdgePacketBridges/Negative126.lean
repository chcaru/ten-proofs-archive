
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative126
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_126 :
    coefficientNegativePacketTerms126 =
      (negativeEdgeTerms.drop 64512).take 512 := by
  unfold coefficientNegativePacketTerms126 coefficientNegativePacketRows126
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
