


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative014
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_014 :
    coefficientNegativePacketTerms014 =
      (negativeEdgeTerms.drop 7168).take 512 := by
  unfold coefficientNegativePacketTerms014 coefficientNegativePacketRows014
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
