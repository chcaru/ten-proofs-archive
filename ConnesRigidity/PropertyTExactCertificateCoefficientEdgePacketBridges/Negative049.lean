
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative049
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_049 :
    coefficientNegativePacketTerms049 =
      (negativeEdgeTerms.drop 25088).take 512 := by
  unfold coefficientNegativePacketTerms049 coefficientNegativePacketRows049
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
