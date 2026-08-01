


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative151
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_151 :
    coefficientNegativePacketTerms151 =
      (negativeEdgeTerms.drop 77312).take 180 := by
  unfold coefficientNegativePacketTerms151 coefficientNegativePacketRows151
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
