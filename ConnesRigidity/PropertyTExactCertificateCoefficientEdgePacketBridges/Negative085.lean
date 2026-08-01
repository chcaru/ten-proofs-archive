
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative085
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_085 :
    coefficientNegativePacketTerms085 =
      (negativeEdgeTerms.drop 43520).take 512 := by
  unfold coefficientNegativePacketTerms085 coefficientNegativePacketRows085
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
