
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive044
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_044 :
    coefficientPositivePacketTerms044 =
      (positiveEdgeTerms.drop 25344).take 576 := by
  unfold coefficientPositivePacketTerms044 coefficientPositivePacketRows044
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
