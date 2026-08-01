
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative013
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_013 :
    coefficientNegativePacketTerms013 =
      (negativeEdgeTerms.drop 6656).take 512 := by
  unfold coefficientNegativePacketTerms013 coefficientNegativePacketRows013
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
