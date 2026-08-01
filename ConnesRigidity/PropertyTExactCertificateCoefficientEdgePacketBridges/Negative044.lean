
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative044
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_044 :
    coefficientNegativePacketTerms044 =
      (negativeEdgeTerms.drop 22528).take 512 := by
  unfold coefficientNegativePacketTerms044 coefficientNegativePacketRows044
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
