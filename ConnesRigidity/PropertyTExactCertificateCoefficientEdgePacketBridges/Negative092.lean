


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative092
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_092 :
    coefficientNegativePacketTerms092 =
      (negativeEdgeTerms.drop 47104).take 512 := by
  unfold coefficientNegativePacketTerms092 coefficientNegativePacketRows092
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
