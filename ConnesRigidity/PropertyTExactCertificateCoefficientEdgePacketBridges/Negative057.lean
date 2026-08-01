


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative057
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_057 :
    coefficientNegativePacketTerms057 =
      (negativeEdgeTerms.drop 29184).take 512 := by
  unfold coefficientNegativePacketTerms057 coefficientNegativePacketRows057
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
