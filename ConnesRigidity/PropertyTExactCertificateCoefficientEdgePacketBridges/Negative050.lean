


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative050
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_050 :
    coefficientNegativePacketTerms050 =
      (negativeEdgeTerms.drop 25600).take 512 := by
  unfold coefficientNegativePacketTerms050 coefficientNegativePacketRows050
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
