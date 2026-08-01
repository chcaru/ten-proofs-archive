


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative004
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_004 :
    coefficientNegativePacketTerms004 =
      (negativeEdgeTerms.drop 2048).take 512 := by
  unfold coefficientNegativePacketTerms004 coefficientNegativePacketRows004
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
