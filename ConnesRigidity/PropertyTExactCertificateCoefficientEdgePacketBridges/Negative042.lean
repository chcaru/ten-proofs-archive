
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative042
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_042 :
    coefficientNegativePacketTerms042 =
      (negativeEdgeTerms.drop 21504).take 512 := by
  unfold coefficientNegativePacketTerms042 coefficientNegativePacketRows042
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
