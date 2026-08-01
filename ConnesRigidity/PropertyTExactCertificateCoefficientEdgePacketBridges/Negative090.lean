
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative090
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_090 :
    coefficientNegativePacketTerms090 =
      (negativeEdgeTerms.drop 46080).take 512 := by
  unfold coefficientNegativePacketTerms090 coefficientNegativePacketRows090
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
