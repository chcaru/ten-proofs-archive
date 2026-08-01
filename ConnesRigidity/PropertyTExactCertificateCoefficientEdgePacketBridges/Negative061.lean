
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative061
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_061 :
    coefficientNegativePacketTerms061 =
      (negativeEdgeTerms.drop 31232).take 512 := by
  unfold coefficientNegativePacketTerms061 coefficientNegativePacketRows061
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
