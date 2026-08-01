
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative040
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_040 :
    coefficientNegativePacketTerms040 =
      (negativeEdgeTerms.drop 20480).take 512 := by
  unfold coefficientNegativePacketTerms040 coefficientNegativePacketRows040
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
