


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative084
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_084 :
    coefficientNegativePacketTerms084 =
      (negativeEdgeTerms.drop 43008).take 512 := by
  unfold coefficientNegativePacketTerms084 coefficientNegativePacketRows084
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
