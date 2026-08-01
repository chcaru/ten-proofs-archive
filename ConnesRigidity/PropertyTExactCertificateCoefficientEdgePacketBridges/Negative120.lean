
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative120
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_120 :
    coefficientNegativePacketTerms120 =
      (negativeEdgeTerms.drop 61440).take 512 := by
  unfold coefficientNegativePacketTerms120 coefficientNegativePacketRows120
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
