
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative027
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_027 :
    coefficientNegativePacketTerms027 =
      (negativeEdgeTerms.drop 13824).take 512 := by
  unfold coefficientNegativePacketTerms027 coefficientNegativePacketRows027
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
