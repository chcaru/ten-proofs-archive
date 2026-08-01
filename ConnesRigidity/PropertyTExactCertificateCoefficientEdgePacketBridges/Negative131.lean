


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative131
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_131 :
    coefficientNegativePacketTerms131 =
      (negativeEdgeTerms.drop 67072).take 512 := by
  unfold coefficientNegativePacketTerms131 coefficientNegativePacketRows131
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
