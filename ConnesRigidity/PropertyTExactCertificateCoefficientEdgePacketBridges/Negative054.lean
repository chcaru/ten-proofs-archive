
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative054
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_054 :
    coefficientNegativePacketTerms054 =
      (negativeEdgeTerms.drop 27648).take 512 := by
  unfold coefficientNegativePacketTerms054 coefficientNegativePacketRows054
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
