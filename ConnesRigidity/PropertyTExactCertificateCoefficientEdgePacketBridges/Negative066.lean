


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative066
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_066 :
    coefficientNegativePacketTerms066 =
      (negativeEdgeTerms.drop 33792).take 512 := by
  unfold coefficientNegativePacketTerms066 coefficientNegativePacketRows066
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
