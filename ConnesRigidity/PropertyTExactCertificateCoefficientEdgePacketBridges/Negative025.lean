


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative025
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_025 :
    coefficientNegativePacketTerms025 =
      (negativeEdgeTerms.drop 12800).take 512 := by
  unfold coefficientNegativePacketTerms025 coefficientNegativePacketRows025
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
