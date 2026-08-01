
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative055
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_055 :
    coefficientNegativePacketTerms055 =
      (negativeEdgeTerms.drop 28160).take 512 := by
  unfold coefficientNegativePacketTerms055 coefficientNegativePacketRows055
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
