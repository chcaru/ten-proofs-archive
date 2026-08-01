
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative082
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_082 :
    coefficientNegativePacketTerms082 =
      (negativeEdgeTerms.drop 41984).take 512 := by
  unfold coefficientNegativePacketTerms082 coefficientNegativePacketRows082
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
