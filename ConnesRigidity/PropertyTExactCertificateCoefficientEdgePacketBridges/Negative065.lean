
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative065
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_065 :
    coefficientNegativePacketTerms065 =
      (negativeEdgeTerms.drop 33280).take 512 := by
  unfold coefficientNegativePacketTerms065 coefficientNegativePacketRows065
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
