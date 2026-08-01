


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative145
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_145 :
    coefficientNegativePacketTerms145 =
      (negativeEdgeTerms.drop 74240).take 512 := by
  unfold coefficientNegativePacketTerms145 coefficientNegativePacketRows145
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
