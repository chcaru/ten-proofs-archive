
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive083
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_083 :
    coefficientPositivePacketTerms083 =
      (positiveEdgeTerms.drop 47808).take 576 := by
  unfold coefficientPositivePacketTerms083 coefficientPositivePacketRows083
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
