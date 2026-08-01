


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative005
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_005 :
    coefficientNegativePacketTerms005 =
      (negativeEdgeTerms.drop 2560).take 512 := by
  unfold coefficientNegativePacketTerms005 coefficientNegativePacketRows005
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
