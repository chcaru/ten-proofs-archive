
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative091
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_091 :
    coefficientNegativePacketTerms091 =
      (negativeEdgeTerms.drop 46592).take 512 := by
  unfold coefficientNegativePacketTerms091 coefficientNegativePacketRows091
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
