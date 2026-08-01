


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative130
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_130 :
    coefficientNegativePacketTerms130 =
      (negativeEdgeTerms.drop 66560).take 512 := by
  unfold coefficientNegativePacketTerms130 coefficientNegativePacketRows130
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
