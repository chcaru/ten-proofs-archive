
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative138
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_138 :
    coefficientNegativePacketTerms138 =
      (negativeEdgeTerms.drop 70656).take 512 := by
  unfold coefficientNegativePacketTerms138 coefficientNegativePacketRows138
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
