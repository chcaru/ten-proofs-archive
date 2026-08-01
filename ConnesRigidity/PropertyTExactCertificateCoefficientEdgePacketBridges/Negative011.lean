


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative011
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_011 :
    coefficientNegativePacketTerms011 =
      (negativeEdgeTerms.drop 5632).take 512 := by
  unfold coefficientNegativePacketTerms011 coefficientNegativePacketRows011
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
