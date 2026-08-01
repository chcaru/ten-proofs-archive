


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative043
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_043 :
    coefficientNegativePacketTerms043 =
      (negativeEdgeTerms.drop 22016).take 512 := by
  unfold coefficientNegativePacketTerms043 coefficientNegativePacketRows043
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
