
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative052
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_052 :
    coefficientNegativePacketTerms052 =
      (negativeEdgeTerms.drop 26624).take 512 := by
  unfold coefficientNegativePacketTerms052 coefficientNegativePacketRows052
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
