
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative106
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_106 :
    coefficientNegativePacketTerms106 =
      (negativeEdgeTerms.drop 54272).take 512 := by
  unfold coefficientNegativePacketTerms106 coefficientNegativePacketRows106
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
