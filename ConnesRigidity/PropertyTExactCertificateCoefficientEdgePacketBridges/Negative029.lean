
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative029
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_029 :
    coefficientNegativePacketTerms029 =
      (negativeEdgeTerms.drop 14848).take 512 := by
  unfold coefficientNegativePacketTerms029 coefficientNegativePacketRows029
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
