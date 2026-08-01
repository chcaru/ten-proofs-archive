
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative123
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_123 :
    coefficientNegativePacketTerms123 =
      (negativeEdgeTerms.drop 62976).take 512 := by
  unfold coefficientNegativePacketTerms123 coefficientNegativePacketRows123
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
