


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative073
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_073 :
    coefficientNegativePacketTerms073 =
      (negativeEdgeTerms.drop 37376).take 512 := by
  unfold coefficientNegativePacketTerms073 coefficientNegativePacketRows073
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
