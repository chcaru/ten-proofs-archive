
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive091
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_091 :
    coefficientPositivePacketTerms091 =
      (positiveEdgeTerms.drop 52416).take 576 := by
  unfold coefficientPositivePacketTerms091 coefficientPositivePacketRows091
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
