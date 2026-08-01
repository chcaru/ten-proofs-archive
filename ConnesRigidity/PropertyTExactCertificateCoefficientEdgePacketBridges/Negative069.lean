


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative069
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_069 :
    coefficientNegativePacketTerms069 =
      (negativeEdgeTerms.drop 35328).take 512 := by
  unfold coefficientNegativePacketTerms069 coefficientNegativePacketRows069
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
