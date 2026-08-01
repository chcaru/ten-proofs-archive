
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive228
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_228 :
    coefficientPositivePacketTerms228 =
      (positiveEdgeTerms.drop 131328).take 576 := by
  unfold coefficientPositivePacketTerms228 coefficientPositivePacketRows228
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
