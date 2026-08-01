
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative136
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_136 :
    coefficientNegativePacketTerms136 =
      (negativeEdgeTerms.drop 69632).take 512 := by
  unfold coefficientNegativePacketTerms136 coefficientNegativePacketRows136
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
