
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative034
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_034 :
    coefficientNegativePacketTerms034 =
      (negativeEdgeTerms.drop 17408).take 512 := by
  unfold coefficientNegativePacketTerms034 coefficientNegativePacketRows034
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
