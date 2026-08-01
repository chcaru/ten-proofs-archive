
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative001
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_001 :
    coefficientNegativePacketTerms001 =
      (negativeEdgeTerms.drop 512).take 512 := by
  unfold coefficientNegativePacketTerms001 coefficientNegativePacketRows001
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
