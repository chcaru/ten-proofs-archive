


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative074
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_074 :
    coefficientNegativePacketTerms074 =
      (negativeEdgeTerms.drop 37888).take 512 := by
  unfold coefficientNegativePacketTerms074 coefficientNegativePacketRows074
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
