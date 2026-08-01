


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative086
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_086 :
    coefficientNegativePacketTerms086 =
      (negativeEdgeTerms.drop 44032).take 512 := by
  unfold coefficientNegativePacketTerms086 coefficientNegativePacketRows086
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
