


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative019
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_019 :
    coefficientNegativePacketTerms019 =
      (negativeEdgeTerms.drop 9728).take 512 := by
  unfold coefficientNegativePacketTerms019 coefficientNegativePacketRows019
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
