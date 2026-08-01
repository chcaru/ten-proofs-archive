
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative132
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_132 :
    coefficientNegativePacketTerms132 =
      (negativeEdgeTerms.drop 67584).take 512 := by
  unfold coefficientNegativePacketTerms132 coefficientNegativePacketRows132
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
