
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative083
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_083 :
    coefficientNegativePacketTerms083 =
      (negativeEdgeTerms.drop 42496).take 512 := by
  unfold coefficientNegativePacketTerms083 coefficientNegativePacketRows083
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
