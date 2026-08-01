


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative059
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_059 :
    coefficientNegativePacketTerms059 =
      (negativeEdgeTerms.drop 30208).take 512 := by
  unfold coefficientNegativePacketTerms059 coefficientNegativePacketRows059
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
