
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative110
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_110 :
    coefficientNegativePacketTerms110 =
      (negativeEdgeTerms.drop 56320).take 512 := by
  unfold coefficientNegativePacketTerms110 coefficientNegativePacketRows110
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
