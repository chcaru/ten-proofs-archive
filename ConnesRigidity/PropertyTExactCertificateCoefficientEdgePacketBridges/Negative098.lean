
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative098
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_098 :
    coefficientNegativePacketTerms098 =
      (negativeEdgeTerms.drop 50176).take 512 := by
  unfold coefficientNegativePacketTerms098 coefficientNegativePacketRows098
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
