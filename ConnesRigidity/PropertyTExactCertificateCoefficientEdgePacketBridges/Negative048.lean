


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative048
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_048 :
    coefficientNegativePacketTerms048 =
      (negativeEdgeTerms.drop 24576).take 512 := by
  unfold coefficientNegativePacketTerms048 coefficientNegativePacketRows048
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
