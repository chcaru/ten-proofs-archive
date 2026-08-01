
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative147
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_147 :
    coefficientNegativePacketTerms147 =
      (negativeEdgeTerms.drop 75264).take 512 := by
  unfold coefficientNegativePacketTerms147 coefficientNegativePacketRows147
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
