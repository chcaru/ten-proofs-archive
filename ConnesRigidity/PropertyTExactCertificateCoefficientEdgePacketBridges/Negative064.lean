
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative064
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_064 :
    coefficientNegativePacketTerms064 =
      (negativeEdgeTerms.drop 32768).take 512 := by
  unfold coefficientNegativePacketTerms064 coefficientNegativePacketRows064
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
