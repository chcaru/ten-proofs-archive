


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative070
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_070 :
    coefficientNegativePacketTerms070 =
      (negativeEdgeTerms.drop 35840).take 512 := by
  unfold coefficientNegativePacketTerms070 coefficientNegativePacketRows070
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
