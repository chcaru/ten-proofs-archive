
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative117
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_117 :
    coefficientNegativePacketTerms117 =
      (negativeEdgeTerms.drop 59904).take 512 := by
  unfold coefficientNegativePacketTerms117 coefficientNegativePacketRows117
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
