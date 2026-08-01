


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative077
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_077 :
    coefficientNegativePacketTerms077 =
      (negativeEdgeTerms.drop 39424).take 512 := by
  unfold coefficientNegativePacketTerms077 coefficientNegativePacketRows077
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
