
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive260
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_260 :
    coefficientPositivePacketTerms260 =
      (positiveEdgeTerms.drop 149760).take 576 := by
  unfold coefficientPositivePacketTerms260 coefficientPositivePacketRows260
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
