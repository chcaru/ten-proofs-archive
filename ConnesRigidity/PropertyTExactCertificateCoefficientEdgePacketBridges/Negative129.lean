


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative129
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_129 :
    coefficientNegativePacketTerms129 =
      (negativeEdgeTerms.drop 66048).take 512 := by
  unfold coefficientNegativePacketTerms129 coefficientNegativePacketRows129
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
