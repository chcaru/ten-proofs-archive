
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative128
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_128 :
    coefficientNegativePacketTerms128 =
      (negativeEdgeTerms.drop 65536).take 512 := by
  unfold coefficientNegativePacketTerms128 coefficientNegativePacketRows128
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
