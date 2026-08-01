
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative028
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_028 :
    coefficientNegativePacketTerms028 =
      (negativeEdgeTerms.drop 14336).take 512 := by
  unfold coefficientNegativePacketTerms028 coefficientNegativePacketRows028
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
