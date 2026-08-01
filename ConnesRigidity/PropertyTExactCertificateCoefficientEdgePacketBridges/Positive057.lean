
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive057
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_057 :
    coefficientPositivePacketTerms057 =
      (positiveEdgeTerms.drop 32832).take 576 := by
  unfold coefficientPositivePacketTerms057 coefficientPositivePacketRows057
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
