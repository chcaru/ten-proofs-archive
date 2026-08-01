
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative063
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_063 :
    coefficientNegativePacketTerms063 =
      (negativeEdgeTerms.drop 32256).take 512 := by
  unfold coefficientNegativePacketTerms063 coefficientNegativePacketRows063
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
