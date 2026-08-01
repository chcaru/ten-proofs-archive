


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative033
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_033 :
    coefficientNegativePacketTerms033 =
      (negativeEdgeTerms.drop 16896).take 512 := by
  unfold coefficientNegativePacketTerms033 coefficientNegativePacketRows033
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
