
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative003
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_003 :
    coefficientNegativePacketTerms003 =
      (negativeEdgeTerms.drop 1536).take 512 := by
  unfold coefficientNegativePacketTerms003 coefficientNegativePacketRows003
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
