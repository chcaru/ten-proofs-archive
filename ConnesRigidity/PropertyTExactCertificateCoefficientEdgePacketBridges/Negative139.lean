
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative139
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_139 :
    coefficientNegativePacketTerms139 =
      (negativeEdgeTerms.drop 71168).take 512 := by
  unfold coefficientNegativePacketTerms139 coefficientNegativePacketRows139
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
