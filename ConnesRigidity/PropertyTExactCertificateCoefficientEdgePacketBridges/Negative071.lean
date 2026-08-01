
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative071
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_071 :
    coefficientNegativePacketTerms071 =
      (negativeEdgeTerms.drop 36352).take 512 := by
  unfold coefficientNegativePacketTerms071 coefficientNegativePacketRows071
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
