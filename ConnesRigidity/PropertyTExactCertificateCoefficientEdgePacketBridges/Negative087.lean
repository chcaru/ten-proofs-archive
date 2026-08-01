
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative087
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_087 :
    coefficientNegativePacketTerms087 =
      (negativeEdgeTerms.drop 44544).take 512 := by
  unfold coefficientNegativePacketTerms087 coefficientNegativePacketRows087
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
