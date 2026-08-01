
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative007
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_007 :
    coefficientNegativePacketTerms007 =
      (negativeEdgeTerms.drop 3584).take 512 := by
  unfold coefficientNegativePacketTerms007 coefficientNegativePacketRows007
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
