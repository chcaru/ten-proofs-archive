
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative127
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_127 :
    coefficientNegativePacketTerms127 =
      (negativeEdgeTerms.drop 65024).take 512 := by
  unfold coefficientNegativePacketTerms127 coefficientNegativePacketRows127
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
