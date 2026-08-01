


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative008
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_008 :
    coefficientNegativePacketTerms008 =
      (negativeEdgeTerms.drop 4096).take 512 := by
  unfold coefficientNegativePacketTerms008 coefficientNegativePacketRows008
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
