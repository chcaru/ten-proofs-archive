
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative089
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_089 :
    coefficientNegativePacketTerms089 =
      (negativeEdgeTerms.drop 45568).take 512 := by
  unfold coefficientNegativePacketTerms089 coefficientNegativePacketRows089
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
