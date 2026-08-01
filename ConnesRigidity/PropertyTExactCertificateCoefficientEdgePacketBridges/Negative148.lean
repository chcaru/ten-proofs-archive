


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative148
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_148 :
    coefficientNegativePacketTerms148 =
      (negativeEdgeTerms.drop 75776).take 512 := by
  unfold coefficientNegativePacketTerms148 coefficientNegativePacketRows148
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
