
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative024
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_024 :
    coefficientNegativePacketTerms024 =
      (negativeEdgeTerms.drop 12288).take 512 := by
  unfold coefficientNegativePacketTerms024 coefficientNegativePacketRows024
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
