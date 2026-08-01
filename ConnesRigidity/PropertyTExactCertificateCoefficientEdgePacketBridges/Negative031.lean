
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative031
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_031 :
    coefficientNegativePacketTerms031 =
      (negativeEdgeTerms.drop 15872).take 512 := by
  unfold coefficientNegativePacketTerms031 coefficientNegativePacketRows031
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
