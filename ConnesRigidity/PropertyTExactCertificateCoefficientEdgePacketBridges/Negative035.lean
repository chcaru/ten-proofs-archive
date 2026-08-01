


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative035
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_035 :
    coefficientNegativePacketTerms035 =
      (negativeEdgeTerms.drop 17920).take 512 := by
  unfold coefficientNegativePacketTerms035 coefficientNegativePacketRows035
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
