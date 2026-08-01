


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative116
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_116 :
    coefficientNegativePacketTerms116 =
      (negativeEdgeTerms.drop 59392).take 512 := by
  unfold coefficientNegativePacketTerms116 coefficientNegativePacketRows116
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
