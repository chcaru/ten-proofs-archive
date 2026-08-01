
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative056
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_056 :
    coefficientNegativePacketTerms056 =
      (negativeEdgeTerms.drop 28672).take 512 := by
  unfold coefficientNegativePacketTerms056 coefficientNegativePacketRows056
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
