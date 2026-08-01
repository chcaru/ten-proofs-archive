


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative080
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_080 :
    coefficientNegativePacketTerms080 =
      (negativeEdgeTerms.drop 40960).take 512 := by
  unfold coefficientNegativePacketTerms080 coefficientNegativePacketRows080
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
