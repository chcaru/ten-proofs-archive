
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative100
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_100 :
    coefficientNegativePacketTerms100 =
      (negativeEdgeTerms.drop 51200).take 512 := by
  unfold coefficientNegativePacketTerms100 coefficientNegativePacketRows100
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
