
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative118
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_118 :
    coefficientNegativePacketTerms118 =
      (negativeEdgeTerms.drop 60416).take 512 := by
  unfold coefficientNegativePacketTerms118 coefficientNegativePacketRows118
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
